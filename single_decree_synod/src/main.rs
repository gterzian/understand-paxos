use automerge_repo::{ConnDirection, DocHandle, DocumentId, Repo, Storage, StorageError};
use autosurgeon::{hydrate, reconcile, Hydrate, Reconcile};
use axum::extract::State;
use axum::routing::get;
use axum::{Json, Router};
use clap::Parser;
use futures::future::BoxFuture;
use futures::FutureExt;
use rand::prelude::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tokio::net::{TcpListener, TcpStream};
use tokio::runtime::Handle;
use tokio::sync::mpsc::{self, Receiver};
use tokio::sync::oneshot::{channel as oneshot, Sender as OneShotSender};
use tokio::sync::Semaphore;
use tokio::time::{sleep, Duration};

async fn get_doc_id(State(state): State<Arc<AppState>>) -> Json<DocumentId> {
    Json(state.doc_handle.document_id())
}

async fn run_proposal_algorithm(doc_handle: &DocHandle, participant_id: &String) {
    loop {
        if rand::random() {
            doc_handle.with_doc_mut(|doc| {
                let mut synod: Synod = hydrate(doc).unwrap();
                let our_info = synod.participants.get_mut(participant_id).unwrap();

                our_info.last_tried.increment();

                let mut tx = doc.transaction();
                reconcile(&mut tx, &synod).unwrap();
                tx.commit();
            });
            continue;
        }

        doc_handle.changed().await.unwrap();

        doc_handle.with_doc_mut(|doc| {
            let mut synod: Synod = hydrate(doc).unwrap();
            let last_tried = synod
                .participants
                .get_mut(participant_id)
                .unwrap()
                .last_tried
                .clone();

            let mut highest_vote = Vote {
                number: Number(0, participant_id.clone()),
                value: Value(0),
            };
            let mut count = 0;
            let mut has_voted = 0;
            for (_id, info) in synod.participants.iter() {
                if info.next_bal == last_tried {
                    count += 1;
                    if let Some(ref vote) = info.prev_vote {
                        if vote.number > highest_vote.number {
                            highest_vote = vote.clone();
                        }
                        if vote.number == last_tried {
                            has_voted += 1;
                        }
                    }
                }
            }

            if count > synod.participants.len() / 2 {
                let value = if let Value(0) = highest_vote.value {
                    let mut rng = rand::thread_rng();
                    Value(rng.gen())
                } else {
                    highest_vote.value.clone()
                };
                let ballot = Ballot {
                    number: last_tried,
                    value,
                };
                if has_voted > synod.participants.len() / 2 {
                    synod.ledger.insert(participant_id.clone(), ballot.value);
                } else {
                    synod.ballots.push(ballot);
                }
            }

            let mut tx = doc.transaction();
            reconcile(&mut tx, &synod).unwrap();
            tx.commit();
        });
    }
}

async fn run_acceptor_algorithm(doc_handle: DocHandle, participant_id: &String) {
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut synod: Synod = hydrate(doc).unwrap();
            let mut next_bal = synod
                .participants
                .get(participant_id)
                .unwrap()
                .next_bal
                .clone();

            for (_id, info) in synod.participants.iter() {
                if info.last_tried > next_bal {
                    next_bal = info.last_tried.clone();
                }
            }

            let mut our_info = synod.participants.get_mut(participant_id).unwrap();

            our_info.next_bal = next_bal;

            for ballot in synod.ballots.iter() {
                if ballot.number == our_info.next_bal {
                    our_info.prev_vote = Some(ballot.clone().into());
                }
            }

            let mut tx = doc.transaction();
            reconcile(&mut tx, &synod).unwrap();
            tx.commit();
        });
        doc_handle.changed().await.unwrap();
    }
}

async fn run_learner_algorithm(doc_handle: DocHandle, participant_id: &String) {
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut synod: Synod = hydrate(doc).unwrap();
            let mut next_bal = synod
                .participants
                .get(participant_id)
                .unwrap()
                .next_bal
                .clone();

            let mut values: HashSet<Value> =
                synod.ledger.iter().map(|(_, val)| val.clone()).collect();
            if !values.is_empty() {
                assert_eq!(values.len(), 1);
                synod
                    .ledger
                    .insert(participant_id.clone(), values.drain().next().unwrap());
            }

            println!("Ledger: {:?}", synod.ledger);

            let mut tx = doc.transaction();
            reconcile(&mut tx, &synod).unwrap();
            tx.commit();
        });
        doc_handle.changed().await.unwrap();
    }
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long)]
    bootstrap: bool,
    #[arg(long)]
    participant_id: String,
}

struct AppState {
    doc_handle: DocHandle,
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq, Ord, PartialOrd)]
struct Number(u32, String);

impl Number {
    fn increment(&mut self) {
        self.0 += 1;
    }
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq)]
struct Value(u32);

#[derive(Debug, Clone, Reconcile, Hydrate, PartialEq)]
struct Vote {
    number: Number,
    value: Value,
}

impl From<Ballot> for Vote {
    fn from(ballot: Ballot) -> Self {
        Vote {
            number: ballot.number,
            value: ballot.value,
        }
    }
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq)]
struct Ballot {
    number: Number,
    value: Value,
}

#[derive(Debug, Clone, Reconcile, Hydrate, PartialEq)]
struct Participant {
    last_tried: Number,
    next_bal: Number,
    prev_vote: Option<Vote>,
}

#[derive(Default, Debug, Clone, Reconcile, Hydrate, PartialEq)]
struct Synod {
    pub participants: HashMap<String, Participant>,
    pub ballots: Vec<Ballot>,
    pub ledger: HashMap<String, Value>,
}

struct NoStorage;

impl Storage for NoStorage {
    fn get(&self, _id: DocumentId) -> BoxFuture<'static, Result<Option<Vec<u8>>, StorageError>> {
        Box::pin(futures::future::ready(Ok(None)))
    }

    fn list_all(&self) -> BoxFuture<'static, Result<Vec<DocumentId>, StorageError>> {
        Box::pin(futures::future::ready(Ok(vec![])))
    }

    fn append(
        &self,
        _id: DocumentId,
        _changes: Vec<u8>,
    ) -> BoxFuture<'static, Result<(), StorageError>> {
        Box::pin(futures::future::ready(Ok(())))
    }

    fn compact(
        &self,
        _id: DocumentId,
        _full_doc: Vec<u8>,
    ) -> BoxFuture<'static, Result<(), StorageError>> {
        Box::pin(futures::future::ready(Ok(())))
    }
}

#[tokio::main]
async fn main() {
    let args = Args::parse();
    let bootstrap = args.bootstrap;
    let participant_id = args.participant_id.clone();
    let handle = Handle::current();

    // All customers, including ourself.
    let customers: Vec<String> = vec!["1", "2", "3"]
        .into_iter()
        .map(|id| id.to_string())
        .collect();

    // Addrs of peers.
    let http_addrs: Vec<String> = customers
        .iter()
        .filter(|id| id != &&args.participant_id)
        .map(|id| format!("0.0.0.0:300{}", id))
        .collect();
    let tcp_addrs: Vec<String> = customers
        .iter()
        .filter(|id| id != &&args.participant_id)
        .map(|id| format!("127.0.0.1:234{}", id))
        .collect();

    // Our addrs
    let our_http_addr = format!("0.0.0.0:300{}", participant_id);
    let our_tcp_addr = format!("127.0.0.1:234{}", participant_id);

    // Create a repo.
    let repo = Repo::new(None, Box::new(NoStorage));
    let repo_handle = repo.run();

    // Start a tcp server.
    let repo_clone = repo_handle.clone();
    handle.spawn(async move {
        let listener = TcpListener::bind(our_tcp_addr).await.unwrap();
        loop {
            match listener.accept().await {
                Ok((socket, addr)) => {
                    repo_clone
                        .connect_tokio_io(addr, socket, ConnDirection::Incoming)
                        .await
                        .unwrap();
                }
                Err(e) => println!("couldn't get client: {:?}", e),
            }
        }
    });

    // Connect to the other peers.
    let repo_clone = repo_handle.clone();
    handle.spawn(async move {
        for addr in tcp_addrs {
            let stream = loop {
                let res = TcpStream::connect(addr.clone()).await;
                if res.is_err() {
                    sleep(Duration::from_millis(100)).await;
                    continue;
                }
                break res.unwrap();
            };
            repo_clone
                .connect_tokio_io(addr, stream, ConnDirection::Outgoing)
                .await
                .unwrap();
        }
    });

    let doc_handle = if bootstrap {
        let mut synod: Synod = Default::default();
        for participant_id in customers.clone() {
            let participant = Participant {
                last_tried: Number(0, participant_id.clone()),
                next_bal: Number(0, participant_id.clone()),
                prev_vote: None,
            };
            synod
                .participants
                .insert(participant_id.to_string(), participant);
        }

        // The initial document.
        let doc_handle = repo_handle.new_document();
        doc_handle.with_doc_mut(|doc| {
            let mut tx = doc.transaction();
            reconcile(&mut tx, &synod).unwrap();
            tx.commit();
        });

        doc_handle
    } else {
        // Get the id of the shared document.
        let client = reqwest::Client::new();
        let mut doc_id = None;
        for addr in http_addrs.iter() {
            let url = format!("http://{}/get_doc_id", addr);
            let res = client.get(url).send().await;
            if res.is_err() {
                continue;
            }
            let data = res.unwrap().json().await;
            if data.is_err() {
                continue;
            }
            doc_id = Some(data.unwrap());
            break;
        }
        assert!(doc_id.is_some());
        // Get the document.
        repo_handle.request_document(doc_id.unwrap()).await.unwrap()
    };

    let app_state = Arc::new(AppState {
        doc_handle: doc_handle.clone(),
    });

    let doc_handle_clone = doc_handle.clone();
    let id = participant_id.clone();
    handle.spawn(async move {
        run_proposal_algorithm(&doc_handle_clone, &id).await;
    });

    let doc_handle_clone = doc_handle.clone();
    let id = participant_id.clone();
    handle.spawn(async move {
        run_acceptor_algorithm(doc_handle_clone, &id).await;
    });

    handle.spawn(async move {
        run_learner_algorithm(doc_handle, &participant_id).await;
    });

    let app = Router::new()
        .route("/get_doc_id", get(get_doc_id))
        .with_state(app_state.clone());
    let serve = axum::Server::bind(&our_http_addr.parse().unwrap()).serve(app.into_make_service());
    tokio::select! {
        _ = serve.fuse() => {},
        _ = tokio::signal::ctrl_c().fuse() => {

            // Clean shutdown:

            // 4. Shutdown the repo.
            Handle::current()
                .spawn_blocking(|| {
                    repo_handle.stop().unwrap();
                })
                .await
                .unwrap();
        }
    }
}
