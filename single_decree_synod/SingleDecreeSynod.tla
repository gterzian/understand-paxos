------------------------- MODULE SingleDecreeSynod -------------------------
EXTENDS FiniteSets, Naturals
VARIABLES lastTried, prevVote, lastVote, replied, nextBal, msgs, ledger, voted
CONSTANT N, MaxTries, NoNumber
----------------------------------------------------------------------------
\* Specification of The Basic Protocol of 2.3 in
\* https://lamport.azurewebsites.net/pubs/lamport-paxos.pdf

IsLowerNumber(a, b) == IF a[1] < b[1] THEN TRUE 
                        ELSE 
                            \* Break ties by participant name.
                            IF a[1] = b[1] THEN a[2] < b[2] 
                            ELSE FALSE

IsHigherNumber(a, b) == IF a[1] > b[1] THEN TRUE 
                        ELSE 
                            \* Break ties by participant name.
                            IF a[1] = b[1] THEN a[2] > b[2] 
                            ELSE FALSE

\* We use N to limit the numbers of participants
Participant == 1..N

\* We also use N to limit the set of numbers that can be chosen.
\*
\* Number is the set of tuples of (participant, participant),
\* ensuring each decree number is unique.
Number == Participant \X Participant

Decree == {NoNumber} \cup Number

ASSUME NoNumber \notin Number

\* The set of possible messages.
Message == [type: {"NextBallot"}, number: Number, src: Participant, dest: Participant]
            \cup
           [type: {"LastVote"}, 
               number: Number, 
               vote: [number: {NoNumber} \cup Number, value: {NoNumber} \cup Number], 
               src: Participant, 
               dest: Participant]
            \cup
           [type: {"BeginBallot"}, 
            number: Number, 
            value: [number: {NoNumber} \cup Number, value: {NoNumber} \cup Number], 
            src: Participant, 
            dest: Participant]
            \cup
           [type: {"Voted"}, number: Number, value: Number, dest: Participant, src: Participant]
            \cup
           [type: {"Success"}, value: Number, dest: Participant]

\* The type invariant.
\*
\* `msgs` is a set, implying messages can be:
\* 1. received in any order
\* 2. duplicated.
TypeOk == /\ msgs \subseteq Message
          /\ lastTried \in [Participant -> {NoNumber} \cup Number]
          /\ nextBal \in [Participant -> {NoNumber} \cup Number] 
          /\ prevVote \in [Participant -> 
            [number: {NoNumber} \cup Number, value: {NoNumber} \cup Number]] 
          /\ lastVote \in [Participant -> [Participant -> 
            [number: {NoNumber} \cup Number, value: {NoNumber} \cup Number]]]  
          /\ replied \in [Participant -> SUBSET Participant]
          /\ voted \in [Participant -> SUBSET Participant]
          /\ ledger \in [Participant -> Decree]

\* The invariant that all ledgers must contain the same decree(or none).
CoherenceInv == \A p \in Participant:
                    \/ ledger[p] = NoNumber
                    \/ ledger[p] \in Number => \A other \in Participant:
                        \/ ledger[p] = ledger[other]
                        \/ ledger[other] = NoNumber 

\* The inductive invariant explaining 
\* why all ledgers must contain the same decree(or none).
PaxosInv == 
     \A p \in Participant:
        LET 
            sameBallot == {i \in Participant: nextBal[i] = nextBal[p]}
            majorityVoted == Cardinality({i \in Participant: prevVote[i].value = ledger[p]}) 
                > (Cardinality(Participant) \div 2)
        IN
        /\ \/ ledger[p] = NoNumber
           \/ ledger[p] \in Number => majorityVoted        
        /\ \A pp \in sameBallot:
           LET 
            otherValueInQuorum == {i \in sameBallot: 
                       \/ prevVote[i].number = nextBal[p] 
                       \/ prevVote[i].value = prevVote[pp].value }
            sameValueInQuorum == {i \in sameBallot: 
                       \/ prevVote[i].number = nextBal[p] 
                       \/ prevVote[i].value = prevVote[p].value }
           IN
           \/ /\ IsLowerNumber(prevVote[pp].number, prevVote[p].number) 
                  => Cardinality(otherValueInQuorum) = 0
              /\ prevVote[pp] # prevVote[p]
           \/ /\ IsHigherNumber(prevVote[pp].number, prevVote[p].number) 
                  => Cardinality(sameValueInQuorum) = 0
              /\ prevVote[pp] # prevVote[p]
           \/ /\ prevVote[pp] = prevVote[p]
           \/ /\prevVote[pp].number = NoNumber                                  
-------------------------------------------------------------------------------------------------------    
    
Init == /\ msgs = {}
        /\ lastTried = [p \in Participant |-> NoNumber]
        /\ nextBal = [p \in Participant |-> NoNumber]
        /\ prevVote = [p \in Participant |-> [number |->  NoNumber, value |-> NoNumber]]
        /\ lastVote = [p \in Participant |-> 
            [pp \in Participant |-> [number |-> NoNumber, value |-> NoNumber]]]
        /\ replied = [p \in Participant |-> {}]
        /\ voted = [p \in Participant |-> {}]
        /\ ledger = [p \in Participant |-> NoNumber]

\* Step 1
ChooseBallotNumber(p) == /\ lastTried[p][1] < MaxTries
                         /\ lastTried' = [lastTried EXCEPT ![p] = <<@[1] + 1, p>>]
                         /\ replied' = [replied EXCEPT ![p] = {}]
                         /\ voted' = [voted EXCEPT ![p] = {}]
                         /\ msgs' = msgs \cup 
                            [type : {"NextBallot"},
                              number: {lastTried'[p]},
                              src: {p}, 
                              dest: Participant]
                         /\ UNCHANGED<<prevVote, nextBal, ledger, lastVote>>

\* Step 2
HandleNextBallot(p) == \E msg \in msgs: 
                        /\ msg.dest = p
                        /\ msg.type = "NextBallot"
                        /\ IsHigherNumber(msg.number, nextBal[p])
                        /\ nextBal' = [nextBal EXCEPT ![p] = msg.number]
                        /\ msgs' = msgs \cup 
                            [type : {"LastVote"},
                              number: {msg.number},
                              vote: {prevVote[p]},
                              src: {p}, 
                              dest: {msg.src}]
                        /\ UNCHANGED<<lastVote, lastTried, prevVote, replied, ledger, voted>>

\* Step 3
HandleLastVote(p) == \E msg \in msgs:   
                        /\ msg.dest = p
                        /\ msg.type = "LastVote"
                        /\ msg.number = lastTried[p]
                        /\ replied' = [replied EXCEPT ![p] = @ \cup {msg.src}]
                        /\ lastVote' = [lastVote EXCEPT ![p][msg.src] = 
                            IF IsHigherNumber(msg.vote.number, @.number) 
                            THEN msg.vote 
                            ELSE @]
                        /\ UNCHANGED<<lastTried, prevVote, nextBal, msgs, ledger, voted>>

\* Step 3 - continued. 
\* Separated in two steps for readeability, 
\* with no impact on correctness.
BeginBallot(p) == LET max[i \in Participant] == 
                                     IF i = 1 THEN lastVote[p][i]
                                     ELSE 
                                        IF IsHigherNumber(lastVote[p][i].number, max[i-1].number) 
                                            THEN lastVote[p][i]
                                        ELSE max[i-1]
                            maxVote == max[N]
                            decree == IF maxVote.value = NoNumber THEN lastTried[p] ELSE maxVote.value
                            hasQuorum == Cardinality(replied[p]) > (Cardinality(Participant) \div 2)
                  IN /\ hasQuorum
                     /\ msgs' = msgs \cup 
                        [type: {"BeginBallot"}, 
                            number: {lastTried[p]}, 
                            value: [
                                number: {lastTried[p]}, 
                                value: {decree}], 
                            src: {p}, 
                            dest: replied[p]]
                     /\ UNCHANGED<<lastTried, lastVote, prevVote,
                                    nextBal, replied, ledger, voted>> 

\* Step 4
HandleBeginBallot(p) == \E msg \in msgs:   
                            /\ msg.dest = p
                            /\ msg.type = "BeginBallot"
                            /\ msg.number = nextBal[p]
                            /\ prevVote' = [prevVote EXCEPT ![p] = msg.value]
                            /\ msgs' = msgs \cup 
                                [type: {"Voted"}, 
                                    number: {msg.number}, 
                                    value: {msg.value.value}, 
                                    src: {p}, 
                                    dest: {msg.src}]
                            /\ UNCHANGED<<lastTried, lastVote, nextBal, replied,ledger, voted>> 

\* Step 5
HandleVoted(p) == \E msg \in msgs: 
                    LET hasQuorum == Cardinality(voted'[p]) > (Cardinality(Participant) \div 2)
                    IN  
                    /\ msg.dest = p
                    /\ msg.type = "Voted" 
                    /\ msg.number = lastTried[p]
                    /\ voted' = [voted EXCEPT ![p] = @ \cup {msg.src}]
                    /\ msgs' = IF hasQuorum
                              THEN msgs \cup 
                                [type: {"Success"}, value: {msg.value}, dest: voted'[p]] 
                              ELSE msgs
                    /\ ledger' = [ledger EXCEPT ![p] = 
                                    IF hasQuorum THEN msg.value ELSE @]
                    /\ UNCHANGED<<lastTried, lastVote, nextBal, replied, prevVote>>

\* Step 6
HandleSuccess(p) == \E msg \in msgs:
                        /\ msg.dest = p
                        /\ msg.type = "Success"
                        /\ ledger[p] = NoNumber
                        /\ ledger' = [ledger EXCEPT ![p] = msg.value]
                        /\ UNCHANGED<<lastTried, lastVote, nextBal,
                                        replied, msgs, prevVote, voted>>

\* The information "kept on a slip of paper", as well as messages, can be lost.
Crash(p) == /\ lastVote' = [lastVote EXCEPT ![p] = 
                [pp \in Participant |-> [number |-> NoNumber, value |-> NoNumber]]]
            /\ replied' = [replied EXCEPT ![p] = {}]
            /\ voted' = [voted EXCEPT ![p] = {}]
            \* Drop all except "NextBallot" messages,
            \* since sending those are limited by MaxTries
            /\ msgs' = {m \in msgs: m.type \in {"NextBallot"}}
            /\ UNCHANGED<<lastTried, nextBal, prevVote, ledger>>
                                                          
Next == \/ \E p \in Participant:
            \/ ChooseBallotNumber(p)
            \/ HandleNextBallot(p)
            \/ HandleLastVote(p)
            \/ BeginBallot(p)
            \/ HandleBeginBallot(p)
            \/ HandleVoted(p)
            \/ HandleSuccess(p)
            \/ Crash(p)                   
=============================================================================

Spec  ==  Init  /\  [][Next]_<<lastTried, lastVote, prevVote, 
                                nextBal, msgs, replied, ledger, voted>>

THEOREM  Spec  =>  [](TypeOk /\ CoherenceInv /\ PaxosInv)
=============================================================================