# Understand Paxos


## The Single-Decree Synod

[Specifying](/single_decree_synod/SingleDecreeSynod.tla), and [implementing](/single_decree_synod/src/main.rs), the Basic Protocol as described in 2.3 of [the original Paxos paper](https://lamport.azurewebsites.net/pubs/lamport-paxos.pdf).

1. Start the bootstap peer:
   - `cargo run -p single_decree_synod --release -- --bootstrap --participant-id "1"`
2. Start two other peers:
   - `cargo run -p single_decree_synod --release --  --participant-id "2"`
   - `cargo run -p single_decree_synod --release --  --participant-id "3"`
3. Watch the peers reach consensus on a single value.

[Understand Paxos with Rust, Automerge, and TLA+ — Part 1: The Synod](https://medium.com/@polyglot_factotum/understand-paxos-with-rust-automerge-and-tla-part-1-the-synod-371df5f16f45)

## Election

[Specifying](/election/Election.tla), and [implementing](election/src/main.rs), leader election for use with a Paxos implementation.

1. Start the bootstap peer:
   - `cargo run -p election --release -- --bootstrap --participant-id "1"`
2. Start two other peers:
   - `cargo run -p election --release --  --participant-id "2"`
   - `cargo run -p election --release --  --participant-id "3"`
3. Watch the peers elect a single "true" leader at all times.

[Understand Paxos with Rust, Automerge, and TLA+ — Part 2: Election](https://medium.com/@polyglot_factotum/understand-paxos-with-rust-automerge-and-tla-part-2-election-4c9314dc90da)

## Multi-Decree

[Specifying](/multi_decree/MultiDecreeParliement.tla), and [implementing](multi_decree/src/main.rs), the Multi-Decree Parliement protocol as described in 3.1 of [the original Paxos paper](https://lamport.azurewebsites.net/pubs/lamport-paxos.pdf).

1. Start the bootstap peer:
   - `cargo run -p multi_decree --release -- --bootstrap --participant-id "1"`
2. Start two other peers:
   - `cargo run -p multi_decree --release --  --participant-id "2"`
   - `cargo run -p multi_decree --release --  --participant-id "3"`
3. Watch the peers reach consensus on a sequence of values, using it to implement a replicated state machine supporting "read" and "increment" operations on a number.

* To periodically simulate a participant crashing, use the `--crash` flag.

[Understand Paxos with Rust, Automerge, and TLA+ — Part 3: Multi-Decree](https://medium.com/@polyglot_factotum/understand-paxos-with-rust-automerge-and-tla-part-3-multi-decree-06c3ca30c663)
