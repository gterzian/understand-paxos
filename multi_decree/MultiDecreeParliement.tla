----------------------- MODULE MultiDecreeParliement -----------------------
EXTENDS FiniteSets, Naturals
VARIABLES leader, lastTried, prevVote, lastVote, replied, nextBal, msgs, ledger, voted, ballots
CONSTANT N, MaxTries, NoNumber, OliveDay
----------------------------------------------------------------------------
IsHigherNumber(a, b) == IF a[1] > b[1] THEN TRUE 
                        ELSE 
                            \* Break ties by participant name.
                            IF a[1] = b[1] THEN a[2] > b[2] 
                            ELSE FALSE

\* We use N to limit the numbers of participants
Participant == 1..N

\* Numbered instances of single-decree algorithms.
Instance == 0..N

\* We also use N to limit the set of numbers that can be chosen.
\*
\* Number is the set of tuples of (decree number, participant),
\* ensuring each decree number is unique.
Number == Participant \X Participant  

Decree ==  Number \cup {OliveDay}

ASSUME NoNumber \notin Number
ASSUME OliveDay \notin Number

Message == [type: {"NextBallot"}, 
            number: Number, 
            src: Participant, 
            dest: Participant]  
            \cup
           [type: {"LastVote"}, 
            number: Number, 
            votes: [Instance -> [number: {NoNumber} \cup Number, 
                                    value: {NoNumber} \cup Number]],
            src: Participant, 
            dest: Participant]  
            \cup
           [type: {"BeginBallot"},
            instance: Instance, 
            number: Number, 
            vote: [number: {NoNumber} \cup Number, 
                    value: Decree], 
            src: Participant, 
            dest: Participant] 
            \cup
           [type: {"Voted"}, 
            instance: Instance, 
            number: Number, 
            value: Decree, 
            dest: Participant, 
            src: Participant]
            \cup
           [type: {"Success"}, 
            src: Participant, 
            instance: Instance,  
            value: Decree, 
            dest: Participant]    

\* The type invariant.
TypeOk == /\ leader \in Participant
          /\ msgs \subseteq Message
          /\ lastTried \in [Participant -> {NoNumber} \cup Number]
          /\ nextBal \in [Participant -> {NoNumber} \cup Number]
          /\ prevVote \in [Participant -> 
                [Instance -> [number: {NoNumber} \cup Number, 
                                value: {NoNumber} \cup Decree]]]
          /\ lastVote \in [Participant ->
                 [Participant -> [Instance ->
                    [number: {NoNumber} \cup Number, 
                        value: {NoNumber} \cup Decree]]]]
          /\ replied \in [Participant -> SUBSET Participant]
          /\ voted \in [Participant -> [Instance -> SUBSET Participant]]
          /\ ledger \in [Participant -> [Instance -> {NoNumber} \cup Decree]]
          /\ ballots \in [Participant -> [Instance -> [value: {NoNumber} \cup Decree, 
                                                        quorum: SUBSET Participant]]]

\* The invariant that, for a given instance, all ledgers must contain the same decree(or none).
CoherenceInv == \A p \in Participant: \E i \in Instance:
                    \/ ledger[p][i] = NoNumber
                    \/ ledger[p][i] \in Decree => \A other \in Participant:
                        \/ ledger[p][i] = ledger[other][i]
                        \/ ledger[other][i] = NoNumber

\* When all participants have reached their max number of tries,
\* all instances should have chosen a value.
ValuesWrittenInv == Cardinality({\A p \in Participant: lastTried[p][1] = MaxTries }) = N =>  
                        \A p \in Participant: \A i \in Instance:
                            /\ ledger[p][i] \in Decree
----------------------------------------------------------------------------

Init == /\ leader = CHOOSE x \in Participant: TRUE
        /\ msgs = {}
        /\ lastTried = [p \in Participant |->  NoNumber]
        /\ nextBal = [p \in Participant |-> NoNumber]
        /\ prevVote = [p \in Participant |-> 
            [i \in Instance |-> [number |->  NoNumber, value |-> NoNumber]]]
        /\ lastVote = [p \in Participant |-> 
            [pp \in Participant |-> 
                [i \in Instance |-> 
                    [number |-> NoNumber, value |-> NoNumber]]]]
        /\ replied = [p \in Participant |-> {}]
        /\ voted = [p \in Participant |-> 
            [i \in Instance |-> {}]]
        /\ ledger = [p \in Participant |-> 
            [i \in Instance |-> NoNumber]]
        /\ ballots = [p \in Participant |-> 
            [i \in Instance |-> [value |-> NoNumber, quorum |-> {}]]]

\* Step 1, with new leader.
ChooseBallotNumber(p) == /\ p # leader
                         /\ leader' = p
                         /\ lastTried[p][1] < MaxTries
                         /\ lastTried' = [lastTried EXCEPT ![p] = <<@[1] + 1, p>>]
                         /\ replied' = [replied EXCEPT ![p] = {}]
                         /\ msgs' = msgs \cup 
                            [type : {"NextBallot"},
                              number: {lastTried'[p]},
                              src: {p}, 
                              dest: Participant]
                         /\ UNCHANGED<<prevVote, nextBal, 
                                voted, ledger, lastVote, ballots>>

\* Step 2
HandleNextBallot(p) == \E msg \in msgs:
                       /\ msg.type = "NextBallot"
                       /\ msg.src = leader 
                       /\ msg.dest = p
                       /\ IsHigherNumber(msg.number, nextBal[p])
                       /\ nextBal' = [nextBal EXCEPT ![p] = msg.number]
                       /\ msgs' = msgs \cup 
                            [type : {"LastVote"},
                              number: {msg.number},
                              votes: {prevVote[p]},
                              src: {p}, 
                              dest: {msg.src}]
                       /\ UNCHANGED<<leader, lastVote, lastTried, prevVote, 
                                replied, ledger, voted, ballots>>
                        
\* Step 3
HandleLastVote(p) == \E msg \in msgs:
                     /\ msg.type = "LastVote"
                     /\ msg.dest = leader  
                     /\ msg.dest = p
                     
                     /\ msg.number = lastTried[p]
                     /\ replied' = [replied EXCEPT ![p] = @ \cup {msg.src}]
                     /\ lastVote' = [lastVote EXCEPT ![p][msg.src] = msg.votes]
                     /\ UNCHANGED<<leader, lastTried, prevVote, nextBal, 
                            msgs, ledger, voted, ballots>>
                        
\* Step 3 - continued. 
\* Separated in two steps for readeability, 
\* with no impact on correctness.
BeginBallot(p, i) == LET max[pp \in Participant] == 
                                     IF pp = 1 THEN lastVote[p][pp][i]
                                     ELSE 
                                        IF IsHigherNumber(
                                                lastVote[p][pp][i].number, max[pp-1].number) 
                                            THEN lastVote[p][pp][i]
                                        ELSE max[pp-1]
                            maxVote == max[N]
                            isLatestInstance == Cardinality({inst \in Instance: inst > i 
                                /\ \E par \in Participant: ledger[par][inst] \in Number}) = 0
                            decree == IF maxVote.value = NoNumber THEN 
                                            IF isLatestInstance THEN lastTried[p]
                                            ELSE OliveDay 
                                      ELSE maxVote.value
                            hasQuorum == Cardinality(replied[p]) 
                                > (Cardinality(Participant) \div 2)
                  IN /\ p = leader
                     /\ hasQuorum
                     /\ ledger[p][i] = NoNumber
                     /\ ballots' = [ballots EXCEPT ![p][i] = 
                        [value |-> decree, quorum |-> replied[p]]]
                     /\ voted' = [voted EXCEPT ![p][i] = {}]
                     /\ msgs' = msgs \cup 
                        [type: {"BeginBallot"}, 
                            instance: {i},
                            number: {lastTried[p]}, 
                            vote: [
                                number: {lastTried[p]}, 
                                value: {decree}], 
                            src: {p}, 
                            dest: replied[p]]
                     /\ UNCHANGED<<leader, lastTried, lastVote, replied, prevVote,
                                    nextBal, ledger>> 

\* Step 4
HandleBeginBallot(p, i) == \E msg \in msgs:
                           /\ msg.type = "BeginBallot"  
                           /\ msg.dest = p
                           /\ msg.src = leader  
                           /\ msg.instance = i
                           /\ msg.number = nextBal[p]
                           /\ IsHigherNumber(nextBal[p], prevVote[p][i].number)
                           /\ prevVote' = [prevVote EXCEPT ![p][i] = msg.vote]
                           /\ msgs' = msgs \cup 
                                [type: {"Voted"},
                                    instance: {i}, 
                                    number: {msg.number},
                                    value: {msg.vote.value}, 
                                    src: {p}, 
                                    dest: {msg.src}]
                            /\ UNCHANGED<<leader, lastTried, lastVote, 
                                nextBal, replied,ledger, voted, ballots>> 
                            
\* Step 5
HandleVoted(p, i) == LET hasQuorum == ballots[p][i].quorum = voted'[p][i]
                          IN 
                    \E msg \in msgs:
                    /\ msg.type = "Voted"
                    /\ msg.instance = i 
                    /\ msg.dest = leader
                    /\ msg.dest = p
                    /\ msg.value = ballots[p][i].value
                    /\ msg.number = lastTried[p]
                    /\ voted' = [voted EXCEPT ![p][i] = @ \cup {msg.src}]
                    /\ msgs' = IF hasQuorum
                              THEN msgs \cup 
                                [type: {"Success"}, 
                                    src: {p}, 
                                    instance: {i}, 
                                    value: {ballots[p][i].value}, 
                                    dest: voted'[p][i]] 
                              ELSE msgs
                    /\ ledger' = [ledger EXCEPT ![p][i] = 
                                    IF hasQuorum THEN ballots[p][i].value ELSE @]
                    /\ UNCHANGED<<leader, lastTried, lastVote, nextBal, 
                        replied, ballots, prevVote>>
                    
\* Step 6
HandleSuccess(p, i) == \E msg \in msgs:
                            /\ msg.type = "Success"
                            /\ msg.instance = i
                            /\ msg.src = leader
                            /\ msg.dest = p
                            /\ ledger[p][i] = NoNumber
                            /\ ledger' = [ledger EXCEPT ![p][i] = msg.value]
                            /\ UNCHANGED<<leader, lastTried, lastVote, nextBal,
                                        replied, msgs, prevVote, ballots, voted>>                    

\* The information "kept on a slip of paper", as well as messages, can be lost.
Crash(p) == /\ lastVote' = [lastVote EXCEPT ![p] = 
                [pp \in Participant |-> 
                    [i \in Instance |-> 
                        [number |-> NoNumber, value |-> NoNumber]]]]
            /\ replied' = [replied EXCEPT ![p] = {}]
            /\ voted' = [voted EXCEPT ![p] = [i \in Instance |-> {}]]
            /\ msgs' = {m \in msgs: m.dest # p}
            /\ ballots' = [ballots EXCEPT ![p] = 
                [i \in Instance |-> [value |-> NoNumber, quorum |-> {}]]]
            /\ UNCHANGED<<leader, lastTried, nextBal, prevVote, ledger>>
                                                          
Next == \E p \in Participant:
           \/ Crash(p)
           \/ ChooseBallotNumber(p)
           \/ HandleNextBallot(p)
           \/ HandleLastVote(p)
           \/ \E i \in Instance:
                \/ BeginBallot(p, i)
                \/ HandleBeginBallot(p, i)
                \/ HandleVoted(p, i)
                \/ HandleSuccess(p, i)  

Spec  ==  Init  /\  [][Next]_<<leader, lastTried, prevVote, lastVote, 
                                    replied, nextBal, msgs, 
                                    ledger, voted, ballots>>

============================================================================
THEOREM  Spec  =>  [](TypeOk /\ CoherenceInv /\ ValuesWrittenInv)
============================================================================