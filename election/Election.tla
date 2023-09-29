------------------------------ MODULE Election ------------------------------
EXTENDS FiniteSets, Naturals, TLC
VARIABLES epochs, leaders, confirmed
CONSTANT N
-----------------------------------------------------------------------------
\* We use N to limit the numbers of participants
Participant == 1..N

\* We use N to limit the number of epochs.
Epoch == 0..N

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

TypeOk == /\ epochs \in [Participant -> [Participant -> Epoch]]
          /\ leaders \in [Participant -> [Participant -> BOOLEAN]]
          /\ confirmed \in SUBSET Participant

WouldAcceptOp(from, to) == \/ /\ to > from  
                              /\ epochs[from][from] > epochs[to][to]
                              /\ leaders[from][from]
                           \/ /\ to < from  
                              /\ epochs[from][from] >= epochs[to][to]

HasSyncedWith(from, to) == /\ epochs[to][from] = epochs[from][from]
                           /\ epochs[from][to] = epochs[to][to]

\* Inductive invariant: why can there be only one true leader?
SingleLeaderSync == \A p \in Participant: 
                        /\ leaders[p][p] => \A pp \in Participant: 
                            /\ (HasSyncedWith(p, pp) /\ leaders[pp][pp]) => pp = p  
                            /\ (HasSyncedWith(p, pp) /\ pp # p) => WouldAcceptOp(p, pp) 

\* Invariant: only one true leader.
SingleTrueLeader == Cardinality(confirmed) \in {0,1}
-----------------------------------------------------------------------------

Init == /\ epochs = [p \in Participant |-> [pp \in Participant |-> 0]]
        /\ leaders = [p \in Participant |-> [pp \in Participant |-> FALSE]]
        /\ confirmed = {}
        
BecomeLeader(p) == LET noHigherLeaderKnown == \A i \in Participant \ {p}: 
                                                  \/ /\ p > i  
                                                     /\ epochs[p][i] =< epochs[p][p]
                                                     /\ leaders[p][i] = FALSE
                                                  \/ /\ p < i  
                                                     /\ epochs[p][i] < epochs[p][p]
                   IN
                   /\ noHigherLeaderKnown
                   /\ epochs[p][p] < Max(Epoch)
                   /\ leaders[p][p] = FALSE
                   /\ leaders' = [leaders EXCEPT ![p][p] = TRUE]
                   /\ epochs' = [epochs EXCEPT ![p][p] = @ + 1]
                   /\ UNCHANGED<<confirmed>>

UpdateView(p) == LET noHigherLeaderGlobally == \A i \in Participant \ {p}:
                                                  \/ /\ p > i  
                                                     /\ epochs[i][i] =< epochs[p][p]
                                                     /\ leaders[i][i] = FALSE
                                                  \/ /\ p < i  
                                                     /\ epochs[i][i] < epochs[p][p]  
                 IN
                 /\ epochs' = [epochs EXCEPT ![p] = [pp \in Participant |-> 
                                CASE pp = p -> Max({epochs[i][i]: i \in Participant})
                                [] OTHER -> epochs[pp][pp]]]
                 /\ leaders' = [leaders EXCEPT ![p] = [i \in Participant |-> 
                                CASE i = p -> IF @[i] = TRUE THEN noHigherLeaderGlobally ELSE FALSE
                                [] OTHER -> IF @[i] = TRUE /\ noHigherLeaderGlobally THEN FALSE ELSE @[i]]]
                 /\ confirmed' = {i \in Participant: leaders'[p][i]}

Heartbeat(p) == /\ epochs[p][p] < Max(Epoch)
                /\ epochs' = [epochs EXCEPT ![p][p] = @ + 1]
                /\ UNCHANGED<<leaders, confirmed>>

Crash(p) == /\ epochs' = [epochs EXCEPT ![p] = [i \in Participant |-> 0]]
            /\ leaders' = [leaders EXCEPT ![p] = [i \in Participant |-> FALSE]]
            /\ UNCHANGED<<confirmed>>
                  
Next == \E p \in Participant: \/ BecomeLeader(p)
                              \/ UpdateView(p)
                              \/ Crash(p)
                              \/ Heartbeat(p)
=============================================================================

Spec  ==  Init  /\  [][Next]_<<epochs, leaders, confirmed>>

THEOREM  Spec  =>  [](TypeOk /\ SingleTrueLeader /\ SingleLeaderSync)
=============================================================================