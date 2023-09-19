# Understand Paxos


## The Single-Decree Synod

[Specifying](/single_decree_synod/SingeDecreeSynod.tla), and [implementing](/single_decree_synod/src/main.rs), the Basic Protocol as described in 2.3 of [the original Paxos paper](https://lamport.azurewebsites.net/pubs/lamport-paxos.pdf).

1. Start the bootstap peer:
   - `cargo run -p single_decree_synod --release -- --bootstrap --participant-id "1"`
2. Start two other peers:
   - `cargo run -p single_decree_synod --release --  --participant-id "2"`
   - `cargo run -p single_decree_synod --release --  --participant-id "3"`
3. Watch the peers reach consensus on a single value.