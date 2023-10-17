use automerge_repo::fs_store::FsStore;
use automerge_repo::{ConnDirection, DocHandle, DocumentId, Repo, Storage, StorageError};
use autosurgeon::{hydrate, reconcile, Hydrate, Reconcile};
use axum::extract::State;
use axum::routing::{get, put};
use axum::{Json, Router};
use clap::Parser;
use futures::future::BoxFuture;
use futures::FutureExt;
use rand::prelude::SliceRandom;
use rand::seq::IteratorRandom;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, VecDeque};
use std::fmt::{Display, Formatter};
use std::sync::{Arc, Mutex};
use tempfile::TempDir;
use tokio::net::{TcpListener, TcpStream};
use tokio::runtime::Handle;
use tokio::sync::mpsc::{self, Receiver, Sender};
use tokio::sync::oneshot;
use tokio::sync::watch;
use tokio::time::{sleep, Duration};

const MAX: usize = 1000;

async fn get_doc_id(State(state): State<Arc<AppState>>) -> Json<DocumentId> {
    Json(state.doc_handle.document_id())
}

async fn read(State(state): State<Arc<AppState>>) -> Json<Option<Value>> {
    let participant_id = state.participant_id.clone();
    let is_leader = state.doc_handle.with_doc_mut(|doc| {
        let mut multi_decree: MultiDecree = hydrate(doc).unwrap();

        // Run election
        let _ = leader_algorithm(&mut multi_decree, &participant_id);

        let our_info = multi_decree.participants.get(&participant_id).unwrap();
        our_info.is_leader
    });

    if !is_leader {
        return Json(None);
    }

    let (tx, rx) = oneshot::channel();
    let _ = state.command_sender.send((ClientCommand::Read, tx)).await;
    Json(rx.await.unwrap_or(None))
}

async fn incr(State(state): State<Arc<AppState>>) -> Json<Option<Value>> {
    let participant_id = state.participant_id.clone();
    let is_leader = state.doc_handle.with_doc_mut(|doc| {
        let mut multi_decree: MultiDecree = hydrate(doc).unwrap();

        // Run election
        let _ = leader_algorithm(&mut multi_decree, &participant_id);

        let our_info = multi_decree.participants.get(&participant_id).unwrap();
        our_info.is_leader
    });

    if !is_leader {
        return Json(None);
    }

    let (tx, rx) = oneshot::channel();
    let _ = state.command_sender.send((ClientCommand::Incr, tx)).await;
    Json(rx.await.unwrap_or(None))
}

fn leader_algorithm(election: &mut MultiDecree, participant_id: &ParticipantId) -> ElectionOutcome {
    let (our_epoch, our_past_leadership) = {
        let our_info = election.participants.get_mut(participant_id).unwrap();
        (our_info.epoch, our_info.is_leader)
    };

    let mut our_new_leadership = true;

    for (id, info) in election.participants.iter_mut() {
        if id == participant_id {
            continue;
        }

        let our_epoch_minus_theirs = our_epoch.saturating_sub(info.epoch);
        if participant_id > id {
            if our_epoch_minus_theirs < 3 && info.is_leader {
                our_new_leadership = false;
            }
        } else if our_epoch_minus_theirs < 3 && !our_past_leadership {
            our_new_leadership = false;
        }
    }

    let outcome = if !our_past_leadership && our_new_leadership {
        ElectionOutcome::NewlyElected
    } else if our_past_leadership && !our_new_leadership {
        ElectionOutcome::SteppedDown
    } else {
        ElectionOutcome::Unchanged
    };

    let max_epoch = election
        .participants
        .values()
        .map(|info| info.epoch)
        .max()
        .unwrap();
    let our_info = election.participants.get_mut(participant_id).unwrap();
    our_info.epoch = if let ElectionOutcome::NewlyElected = outcome {
        max_epoch + 1
    } else {
        max_epoch
    };
    our_info.is_leader = our_new_leadership;
    outcome
}

fn execute_state_machine(
    ballot_number_to_client_command: &mut [Option<oneshot::Sender<Option<Value>>>],
    log: Vec<Option<Ballot>>,
) {
    let mut start = 0;

    if let Some(can_execute_up_to) = log.iter().position(|x| x.is_none()) {
        for index in 0..MAX {
            if index >= can_execute_up_to {
                return;
            }
            let cmd = log[index].as_ref().unwrap().value.clone();
            let new_execution = match cmd {
                ClientCommand::Read => ballot_number_to_client_command[index].take(),
                ClientCommand::Incr => {
                    start += 1;
                    ballot_number_to_client_command[index].take()
                }
                _ => continue,
            };
            if let Some(chan) = new_execution {
                chan.send(Some(Value(start))).unwrap();
            }
        }
    }
}

async fn run_proposal_algorithm(
    doc_handle: &DocHandle,
    participant_id: &ParticipantId,
    indices: Vec<usize>,
    mut command_receiver: Receiver<(ClientCommand, oneshot::Sender<Option<Value>>)>,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    let mut pending_client_commands: VecDeque<(ClientCommand, oneshot::Sender<Option<Value>>)> =
        Default::default();
    let mut ballot_number_to_client_command: Vec<Option<oneshot::Sender<Option<Value>>>> = vec![];
    for _ in 0..MAX {
        ballot_number_to_client_command.push(None);
    }
    loop {
        let indices = indices.clone();
        doc_handle.with_doc_mut(|doc| {
            let mut multi_decree: MultiDecree = hydrate(doc).unwrap();

            // Run election
            let outcome = leader_algorithm(&mut multi_decree, participant_id);
            if let ElectionOutcome::NewlyElected = outcome {
                println!("Elected");

                let max_tried = multi_decree
                    .participants
                    .values()
                    .map(|p| p.last_tried.0)
                    .max()
                    .unwrap_or(0);
                let our_info = multi_decree.participants.get_mut(participant_id).unwrap();

                // Only if newly elected as leader:
                // Step 1: ChooseBallotNumber.
                our_info.last_tried = Number(
                    max_tried.checked_add(1).unwrap_or(0),
                    our_info.last_tried.1.clone(),
                );
            } else if let ElectionOutcome::SteppedDown = outcome {
                println!("stepping down");
                // Reset the client command state,
                // send back None to all pending commands.
                pending_client_commands.drain(..).for_each(|(_, chan)| {
                    chan.send(None).unwrap();
                });
                for chan in ballot_number_to_client_command.iter_mut() {
                    if let Some(chan) = chan.take() {
                        chan.send(None).unwrap();
                    }
                }
            }

            let participants = multi_decree.participants.clone();
            let our_info = multi_decree.participants.get_mut(participant_id).unwrap();

            // Reset older ballots.
            for ballot in our_info.ballot.iter_mut() {
                if let Some(b) = ballot {
                    if b.number < our_info.last_tried {
                        *ballot = None;
                    }
                }
            }

            if our_info.is_leader && our_info.log.iter().filter(|i| i.is_some()).count() < MAX {
                for index in indices {
                    // If we already have a value in the log.
                    if our_info.log.get(index).unwrap().is_some() {
                        continue;
                    }
                    if let Some(ref mut ballot) = our_info.ballot.get_mut(index).unwrap() {
                        // Step 5: HandleVoted.
                        for (id, info) in participants.iter() {
                            if !ballot.quorum.contains_key(id) {
                                continue;
                            }
                            if let Some(ref vote) = info.prev_vote.get(index).unwrap() {
                                if vote.number == ballot.number {
                                    let val = vote.value.as_ref().unwrap();
                                    if val == &ballot.value {
                                        ballot.quorum.insert(id.clone(), true);
                                    }
                                }
                            }
                        }
                        let vote_count = ballot.quorum.iter().filter(|(_, voted)| **voted).count();
                        if vote_count > participants.len() / 2 {
                            our_info.log[index] = Some(ballot.clone());

                            // Execute state machine
                            execute_state_machine(
                                &mut ballot_number_to_client_command,
                                our_info.log.clone(),
                            );
                        }
                    } else {
                        // Step 3: HandleLastVote.
                        let mut replied: HashMap<ParticipantId, Option<Vote>> = Default::default();
                        for (id, info) in participants.iter() {
                            if info.next_bal == our_info.last_tried {
                                replied.insert(
                                    id.clone(),
                                    info.prev_vote.get(index).cloned().flatten(),
                                );
                            }
                        }
                        if replied.len() > participants.len() / 2 {
                            // Step 3 (cont'd): BeginBallot.
                            let mut highest_vote = Vote {
                                number: Number(0, participant_id.clone()),
                                value: None,
                            };
                            for vote in replied.iter().filter_map(|(_, v)| v.clone()) {
                                if vote.number > highest_vote.number {
                                    highest_vote = vote.clone();
                                }
                            }

                            let number = our_info.last_tried.clone();
                            let value = if highest_vote.value.is_none() {
                                let highest_entry = our_info
                                    .log
                                    .iter()
                                    .enumerate()
                                    .filter_map(|(idx, entry)| entry.as_ref().map(|_| idx))
                                    .max()
                                    .unwrap_or(0);
                                println!("Index: {:?}, highest entry: {:?}", index, highest_entry);
                                if index < highest_entry {
                                    println!("Filling in gaps");
                                    // Filling in gaps
                                    ClientCommand::NoOp
                                } else {
                                    // Assigning a client command as the value to be voted on.
                                    if let Some((cmd, chan)) = pending_client_commands.pop_front() {
                                        ballot_number_to_client_command[index] = Some(chan);
                                        cmd
                                    } else {
                                        break;
                                    }
                                }
                            } else {
                                highest_vote.value.unwrap()
                            };
                            let ballot = Ballot {
                                number,
                                value,
                                quorum: replied.into_keys().map(|id| (id, false)).collect(),
                            };
                            our_info.ballot[index] = Some(ballot);
                        }
                    }
                }
            }
            let mut tx = doc.transaction();
            reconcile(&mut tx, &multi_decree).unwrap();
            tx.commit();
        });
        tokio::select! {
            cmd = command_receiver.recv() => {
                if let Some(cmd) = cmd {
                    pending_client_commands.push_back(cmd);
                } else {
                        return;
                }
            }
            _ = doc_handle.changed() => {},
            _ = shutdown.changed() => return,
        };
    }
}

async fn run_acceptor_algorithm(
    doc_handle: DocHandle,
    participant_id: &ParticipantId,
    indices: Vec<usize>,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    loop {
        let indices = indices.clone();
        doc_handle.with_doc_mut(|doc| {
            let mut multi_decree: MultiDecree = hydrate(doc).unwrap();

            let mut next_bal = multi_decree
                .participants
                .get(participant_id)
                .unwrap()
                .next_bal
                .clone();

            let mut prev_vote = multi_decree
                .participants
                .get_mut(participant_id)
                .unwrap()
                .prev_vote
                .clone();

            for info in multi_decree.participants.values() {
                if info.last_tried > next_bal {
                    // Step 2: HandleNextBallot.
                    next_bal = info.last_tried.clone();
                }

                for index in indices.clone() {
                    if let Some(ref ballot) = info.ballot[index] {
                        // Step 4: HandleBeginBallot.
                        if ballot.number == next_bal {
                            prev_vote[index] = Some(ballot.clone().into());
                        }
                    }
                }
            }

            let our_info = multi_decree.participants.get_mut(participant_id).unwrap();
            our_info.next_bal = next_bal;
            our_info.prev_vote = prev_vote;

            let mut tx = doc.transaction();
            reconcile(&mut tx, &multi_decree).unwrap();
            tx.commit();
        });
        tokio::select! {
            _ = doc_handle.changed() => {},
            _ = shutdown.changed() => return,
        };
    }
}

async fn run_learner_algorithm(
    doc_handle: DocHandle,
    participant_id: ParticipantId,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut multi_decree: MultiDecree = hydrate(doc).unwrap();

            let logs: Vec<Vec<Option<Ballot>>> = multi_decree
                .participants
                .values()
                .map(|info| info.log.clone())
                .collect();

            let our_info = multi_decree.participants.get_mut(&participant_id).unwrap();
            for log in logs {
                for (index, entry) in log.into_iter().enumerate() {
                    let our_entry = &mut our_info.log[index];
                    if our_entry.is_some() && entry.is_some() {
                        // Check integrity.
                        assert_eq!(entry.unwrap().value, our_entry.as_ref().unwrap().value);
                    } else if entry.is_some() && our_entry.is_none() {
                        // Step 6: HandleSuccess.
                        *our_entry = entry;
                    }
                }
            }

            let mut tx = doc.transaction();
            reconcile(&mut tx, &multi_decree).unwrap();
            tx.commit();
        });
        tokio::select! {
            _ = doc_handle.changed() => {},
            _ = shutdown.changed() => return,
        };
    }
}

async fn run_heartbeat_algorithm(
    doc_handle: DocHandle,
    participant_id: ParticipantId,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    loop {
        doc_handle.with_doc_mut(|doc| {
            let mut multi_decree: MultiDecree = hydrate(doc).unwrap();

            let our_info = multi_decree.participants.get_mut(&participant_id).unwrap();
            our_info.epoch = our_info.epoch.checked_add(1).unwrap_or(0);

            let mut tx = doc.transaction();
            reconcile(&mut tx, &multi_decree).unwrap();
            tx.commit();
        });
        tokio::select! {
            _ = sleep(Duration::from_millis(3000)) => {},
            _ = shutdown.changed() => return,
        };
    }
}

async fn run_crash_algorithm(
    doc_handle: DocHandle,
    participant_id: ParticipantId,
    crash: bool,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    loop {
        tokio::select! {
            _ = sleep(Duration::from_millis(10000)) => {},
            _ = shutdown.changed() => return,
        };
        doc_handle.with_doc_mut(|doc| {
            let mut multi_decree: MultiDecree = hydrate(doc).unwrap();

            let our_info = multi_decree.participants.get_mut(&participant_id).unwrap();
            if our_info.is_leader && rand::random() && crash {
                our_info.epoch = 0;
                our_info.ballot = vec![None; MAX];
                println!("Crash start");

                use std::{thread, time};

                let ten_secs = time::Duration::from_millis(20000);

                thread::sleep(ten_secs);

                println!("Re-starting");
            }

            let mut tx = doc.transaction();
            reconcile(&mut tx, &multi_decree).unwrap();
            tx.commit();
        });
    }
}

async fn request_increment(
    http_addrs: Vec<String>,
    mut shutdown: tokio::sync::watch::Receiver<()>,
) {
    let client = reqwest::Client::new();
    let mut last = 0;
    loop {
        for addr in http_addrs.iter() {
            tokio::select! {
                _ = sleep(Duration::from_millis(1000)) => {},
                _ = shutdown.changed() => return,
            };
            let url = format!("http://{}/incr", addr);
            let res = client.put(url).send().await;
            if let Ok(new) = res {
                let json_res = new.json().await;
                if let Ok(Some(new)) = json_res {
                    println!("Got new increment: {:?}, versus old one: {:?}", new, last);
                    assert!(new > last);
                    last = new;
                }
            }
        }
    }
}

async fn request_read(http_addrs: Vec<String>, mut shutdown: tokio::sync::watch::Receiver<()>) {
    let client = reqwest::Client::new();
    let mut last = 0;
    loop {
        for addr in http_addrs.iter() {
            tokio::select! {
                _ = sleep(Duration::from_millis(1000)) => {},
                _ = shutdown.changed() => return,
            };
            let url = format!("http://{}/read", addr);
            let res = client.get(url).send().await;
            if let Ok(new) = res {
                let json_res = new.json().await;
                if let Ok(Some(new)) = json_res {
                    println!("Got new read: {:?}, versus old one: {:?}", new, last);
                    assert!(new >= last);
                    last = new;
                }
            }
        }
    }
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(long)]
    bootstrap: bool,
    #[arg(long)]
    random: bool,
    #[arg(long)]
    crash: bool,
    #[arg(long)]
    participant_id: String,
}

struct AppState {
    doc_handle: DocHandle,
    command_sender: Sender<(ClientCommand, oneshot::Sender<Option<Value>>)>,
    participant_id: ParticipantId,
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq)]
enum ClientCommand {
    Read,
    Incr,
    NoOp,
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq, Ord, PartialOrd)]
struct Number(u64, ParticipantId);

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq, Deserialize, Serialize)]
struct Value(u64);

#[derive(Debug, Clone, Reconcile, Hydrate)]
struct Vote {
    number: Number,
    value: Option<ClientCommand>,
}

impl From<Ballot> for Vote {
    fn from(ballot: Ballot) -> Self {
        Vote {
            number: ballot.number,
            value: Some(ballot.value),
        }
    }
}

#[derive(Debug, Clone, Reconcile, Hydrate)]
struct Ballot {
    number: Number,
    value: ClientCommand,
    quorum: HashMap<ParticipantId, bool>,
}

#[derive(Debug, PartialEq)]
enum ElectionOutcome {
    NewlyElected,
    SteppedDown,
    Unchanged,
}

#[derive(Debug, Clone, Reconcile, Hydrate, Eq, Hash, PartialEq, PartialOrd, Ord)]
struct ParticipantId(String);

impl Display for ParticipantId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<str> for ParticipantId {
    #[inline(always)]
    fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}

impl From<String> for ParticipantId {
    fn from(s: String) -> Self {
        Self(s)
    }
}

#[derive(Debug, Clone, Reconcile, Hydrate)]
struct Participant {
    /// Consensus data.
    last_tried: Number,
    next_bal: Number,
    prev_vote: Vec<Option<Vote>>,
    ballot: Vec<Option<Ballot>>,
    log: Vec<Option<Ballot>>,

    /// Election data.
    epoch: u64,
    is_leader: bool,
}

#[derive(Default, Debug, Clone, Reconcile, Hydrate)]
struct MultiDecree {
    participants: HashMap<ParticipantId, Participant>,
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
        Box::new(BlockingFsStorage(Arc::new(Mutex::new(store)))),
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
        let mut multi_decree: MultiDecree = Default::default();
        for participant_id in customers.clone() {
            let participant = Participant {
                last_tried: Number(0, ParticipantId(participant_id.clone())),
                next_bal: Number(0, ParticipantId(participant_id.clone())),
                prev_vote: vec![None; MAX],
                ballot: vec![None; MAX],
                log: vec![None; MAX],
                epoch: 0,
                is_leader: false,
            };
            multi_decree
                .participants
                .insert(ParticipantId(participant_id.to_string()), participant);
        }

        // The initial document.
        let doc_handle = repo_handle.new_document();
        doc_handle.with_doc_mut(|doc| {
            let mut tx = doc.transaction();
            reconcile(&mut tx, &multi_decree).unwrap();
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

    let participant_id = ParticipantId(participant_id);

    let (tx, rx) = mpsc::channel(100);

    let app_state = Arc::new(AppState {
        doc_handle: doc_handle.clone(),
        command_sender: tx,
        participant_id: participant_id.clone(),
    });

    let (shutdown_tx, shutdown_rx) = watch::channel(());

    let indices = {
        if args.random {
            let mut rng = rand::thread_rng();
            let mut indices = (0..MAX).choose_multiple(&mut rng, MAX);
            indices.shuffle(&mut rng);
            indices
        } else {
            (0..MAX).collect()
        }
    };

    let doc_handle_clone = doc_handle.clone();
    let id = participant_id.clone();
    let shutdown = shutdown_rx.clone();
    let indices_clone = indices.clone();
    let proposer = handle.spawn(async move {
        run_proposal_algorithm(&doc_handle_clone, &id, indices_clone, rx, shutdown).await;
    });

    let doc_handle_clone = doc_handle.clone();
    let id = participant_id.clone();
    let shutdown = shutdown_rx.clone();
    let acceptor = handle.spawn(async move {
        run_acceptor_algorithm(doc_handle_clone, &id, indices, shutdown).await;
    });

    let doc_handle_clone = doc_handle.clone();
    let id = participant_id.clone();
    let shutdown = shutdown_rx.clone();
    let heartbeat = handle.spawn(async move {
        run_heartbeat_algorithm(doc_handle_clone, id, shutdown).await;
    });

    let doc_handle_clone = doc_handle.clone();
    let id = participant_id.clone();
    let shutdown = shutdown_rx.clone();
    let learner = handle.spawn(async move {
        run_learner_algorithm(doc_handle_clone, id, shutdown).await;
    });

    let http_addrs_clone = http_addrs.clone();
    let shutdown = shutdown_rx.clone();
    let incrementer = handle.spawn(async move {
        // Continuously request new increments.
        request_increment(http_addrs_clone, shutdown).await;
    });

    let shutdown = shutdown_rx.clone();
    let reader = handle.spawn(async move {
        // Continuously request new reads.
        request_read(http_addrs, shutdown).await;
    });

    let shutdown = shutdown_rx.clone();
    let crasher = handle.spawn(async move {
        run_crash_algorithm(doc_handle, participant_id, args.crash, shutdown).await;
    });

    let app = Router::new()
        .route("/get_doc_id", get(get_doc_id))
        .route("/read", get(read))
        .route("/incr", put(incr))
        .with_state(app_state.clone());
    let serve = axum::Server::bind(&our_http_addr.parse().unwrap()).serve(app.into_make_service());
    tokio::select! {
        _ = serve.fuse() => {},
        _ = tokio::signal::ctrl_c().fuse() => {

            // Send shutdown signal.
            shutdown_tx.send(()).unwrap();

            // Join on tasks.
            incrementer.await.unwrap();
            reader.await.unwrap();
            proposer.await.unwrap();
            acceptor.await.unwrap();
            heartbeat.await.unwrap();
            learner.await.unwrap();
            crasher.await.unwrap();

            // Stop repo.
            Handle::current()
                .spawn_blocking(|| {
                    repo_handle.stop().unwrap();
                })
                .await
                .unwrap();
        }
    }
}
