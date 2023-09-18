use automerge_repo::{ConnDirection, DocHandle, DocumentId, Repo, Storage, StorageError};
use autosurgeon::{hydrate, reconcile, Hydrate, Reconcile};
use axum::extract::State;
use axum::routing::get;
use axum::{Json, Router};
use clap::Parser;
use futures::future::BoxFuture;
use futures::FutureExt;
use std::collections::HashMap;
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
    
}

async fn run_acceptor_algorithm(doc_handle: DocHandle, participant_id: String) {

}

async fn run_learner_algorithm(doc_handle: DocHandle, participant_id: String) {

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

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq)]
struct Number(String, u32);

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq)]
struct Value(u32);

#[derive(Debug, Clone, Reconcile, Hydrate, PartialEq)]
struct Vote {
    number: Number,
    value: Value,
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq)]
struct Ballot {
    number: Number,
    value: Value,
}

#[derive(Default, Debug, Clone, Reconcile, Hydrate, PartialEq)]
struct Participant {
    lastTried: Option<Number>,
    nextBal: Option<Number>,
    prevVote: Option<Vote>,
}

#[derive(Default, Debug, Clone, Reconcile, Hydrate, PartialEq)]
struct Synod {
    pub participants: HashMap<String, Participant>,
    pub ballots: HashMap<String, Ballot>,
    pub votes: HashMap<String, Vote>,
    pub ledger: HashMap<String, Value>,
    pub closing: bool,
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
        let mut synod: Synod = Synod {
            closing: false,
            ..Default::default()
        };
        for participant_id in customers.clone() {
            synod.participants.insert(participant_id.to_string(), Default::default());
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
        run_acceptor_algorithm(doc_handle_clone, id).await;
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
