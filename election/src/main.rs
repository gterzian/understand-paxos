use automerge_repo::fs_store::FsStore;
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
use std::sync::{Arc, Mutex};
use tokio::net::{TcpListener, TcpStream};
use tokio::runtime::Handle;
use tokio::time::{sleep, Duration};
use tempfile::TempDir;

async fn get_doc_id(State(state): State<Arc<AppState>>) -> Json<DocumentId> {
    Json(state.doc_handle.document_id())
}

async fn run_proposal_algorithm(doc_handle: &DocHandle, participant_id: &String) {
    doc_handle.with_doc_mut(|doc| {
        let mut synod: Synod = hydrate(doc).unwrap();
        let our_info = synod.participants.get_mut(participant_id).unwrap();

        // Step 1: ChooseBallotNumber.
        our_info.last_tried.increment();

        let mut tx = doc.transaction();
        reconcile(&mut tx, &synod).unwrap();
        tx.commit();
    });
    loop {
        // Randomly start a new try.
        if rand::random() {
            doc_handle.with_doc_mut(|doc| {
                let mut synod: Synod = hydrate(doc).unwrap();
                let our_info = synod.participants.get_mut(participant_id).unwrap();
                
                // Stop trying once we've written a value to our ledger.
                if synod.ledger.contains_key(participant_id) {
                    return;
                }

                // Step 1: ChooseBallotNumber.
                our_info.last_tried.increment();

                let mut tx = doc.transaction();
                reconcile(&mut tx, &synod).unwrap();
                tx.commit();
            });
        }
        
        doc_handle.changed().await.unwrap();

        doc_handle.with_doc_mut(|doc| {
            let mut synod: Synod = hydrate(doc).unwrap();
            let participants = synod.participants.clone();
            let our_info = synod.participants.get_mut(participant_id).unwrap();

            if let Some(ref mut ballot) = our_info.ballot {
                if ballot.number < our_info.last_tried {
                    // Forget about older ballots.
                    our_info.ballot = None;
                } else {
                    // Step 5: HandleVoted.
                    for (id, info) in participants.iter() {
                        if !ballot.quorum.contains_key(id) {
                            continue;
                        }
                        if let Some(ref vote) = info.prev_vote {
                            if vote.number == ballot.number && vote.value == ballot.value {
                                ballot.quorum.insert(id.clone(), true);
                            }
                        }
                    }
                    let vote_count = ballot.quorum.iter().filter(|(_, voted)| **voted).count();
                    if vote_count > participants.len() / 2 {
                        synod
                            .ledger
                            .insert(participant_id.clone(), ballot.value.clone());
                    }
                }        
            } else {
                // Step 3: HandleLastVote.
                let mut replied: HashMap<String, Option<Vote>> = Default::default();
                for (id, info) in participants.iter() {
                    if info.next_bal == our_info.last_tried {
                        replied.insert(id.clone(), info.prev_vote.clone());
                    }
                }
                if replied.len() > participants.len() / 2 {
                    // Step 3 (cont'd): BeginBallot.
                    let mut highest_vote = Vote {
                        number: Number(0, participant_id.clone()),
                        value: Value(0),
                    };
                    for vote in replied.iter().filter_map(|(_, v)| v.clone()) {
                        if vote.number > highest_vote.number {
                            highest_vote = vote.clone();
                        }
                    }
                    let value = if let Value(0) = highest_vote.value {
                        let mut rng = rand::thread_rng();
                        Value(rng.gen())
                    } else {
                        highest_vote.value
                    };
                    let ballot = Ballot {
                        number: our_info.last_tried.clone(),
                        value,
                        quorum: replied.into_iter().map(|(id, _)| (id, false)).collect(),
                    };
                    our_info.ballot = Some(ballot);
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
                    // Step 2: HandleNextBallot.
                    next_bal = info.last_tried.clone();
                }
            }

            let mut prev_vote = synod
                .participants
                .get_mut(participant_id)
                .unwrap()
                .prev_vote
                .clone();
            for (_id, info) in synod.participants.iter() {
                if let Some(ref ballot) = info.ballot {
                    // Step 4: HandleBeginBallot.
                    if ballot.number == next_bal {
                        if let Some(ref vote) = prev_vote {
                            if ballot.number > vote.number {
                                prev_vote = Some(ballot.clone().into());
                            }
                        } else {
                            prev_vote = Some(ballot.clone().into());
                        }
                    }
                }
            }

            let our_info = synod.participants.get_mut(participant_id).unwrap();
            our_info.next_bal = next_bal;
            our_info.prev_vote = prev_vote;

            let mut tx = doc.transaction();
            reconcile(&mut tx, &synod).unwrap();
            tx.commit();
        });
        doc_handle.changed().await.unwrap();
    }
}

async fn run_learner_algorithm(doc_handle: DocHandle, participant_id: String) {
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut synod: Synod = hydrate(doc).unwrap();
            let mut values: HashSet<Value> = synod.ledger.values().cloned().collect();
            if !values.is_empty() {
                assert_eq!(values.len(), 1);

                // Step 6: HandleSuccess.
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

#[derive(Debug, Clone, Reconcile, Hydrate)]
struct Ballot {
    number: Number,
    value: Value,
    quorum: HashMap<String, bool>,
}

#[derive(Debug, Clone, Reconcile, Hydrate)]
struct Participant {
    last_tried: Number,
    next_bal: Number,
    prev_vote: Option<Vote>,
    ballot: Option<Ballot>,
}

#[derive(Default, Debug, Clone, Reconcile, Hydrate)]
struct Synod {
    pub participants: HashMap<String, Participant>,
    pub ledger: HashMap<String, Value>,
}

struct BlockingFsStorage(Arc<Mutex<FsStore>>);

impl Storage for BlockingFsStorage {
    fn get(&self, id: DocumentId) -> BoxFuture<'static, Result<Option<Vec<u8>>, StorageError>> {
        Box::pin(futures::future::ready(
            self.0
                .lock()
                .unwrap()
                .get(&id)
                .map_err(move |_| StorageError::Error),
        ))
    }

    fn list_all(&self) -> BoxFuture<'static, Result<Vec<DocumentId>, StorageError>> {
        Box::pin(futures::future::ready(
            self.0
                .lock()
                .unwrap()
                .list()
                .map_err(move |_| StorageError::Error),
        ))
    }

    fn append(
        &self,
        id: DocumentId,
        changes: Vec<u8>,
    ) -> BoxFuture<'static, Result<(), StorageError>> {
        Box::pin(futures::future::ready(
            self.0
                .lock()
                .unwrap()
                .append(&id, &changes)
                .map_err(move |_| StorageError::Error),
        ))
    }

    fn compact(
        &self,
        id: DocumentId,
        full_doc: Vec<u8>,
    ) -> BoxFuture<'static, Result<(), StorageError>> {
        Box::pin(futures::future::ready(
            self.0
                .lock()
                .unwrap()
                .compact(&id, &full_doc)
                .map_err(move |_| StorageError::Error),
        ))
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
    let temp_dir = TempDir::new().unwrap();
    let store = FsStore::open(temp_dir.path()).unwrap();
    let repo = Repo::new(
        None,
        Box::new(BlockingFsStorage(Arc::new(Mutex::new(
            store
        )))),
    );
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
                ballot: None,
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
        run_learner_algorithm(doc_handle, participant_id).await;
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