--------------------------- MODULE CassandraPaxos ---------------------------
(*
This is a high-level specification of the CassandraPaxos algorithm
used by Cassandra to implement LWT (lightweight transactions).

This spec is adapted from that of Paxos consensus algorithm by Leslie Lamport,
which can be found at https://github.com/tlaplus/Examples/blob/master/specifications/PaxosHowToWinATuringAward/Paxos.tla.
*)
EXTENDS Integers
-----------------------------------------------------------------------------
CONSTANTS
    Value,      \* the set of values to be proposed and chosen from
    Acceptor,   \* the set acceptors
    Quorum,     \* the quorum system on acceptors
    Ballot

None == CHOOSE v : v \notin Value 

ASSUME  /\ \A Q \in Quorum : Q \subseteq Acceptor
        /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
-----------------------------------------------------------------------------


(*
<<+>> The set of all possible CAS operations.
The CAS operations with cmpVal = None are initialization operations.
We assume that the new values (i.e., swapVal) are not None.
*)
CASOperation == [cmpVal : Value \cup {None}, swapVal : Value]

Message == \* the set of all possible messages that can be sent in the algorithm
       [type : {"1a"}, bal : Ballot]
  \cup [type : {"1b"}, acc : Acceptor, bal : Ballot]
  \cup [type : {"2a"}, bal : Ballot]
  \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value \cup {None}]
  \cup [type : {"3a"}, bal : Ballot, val : Value]
  \cup [type : {"3b"}, acc : Acceptor, bal : Ballot, val : Value]
  \cup [type : {"response"}, bal : Ballot]  \* <<+>> the messages sent to the user
-----------------------------------------------------------------------------
VARIABLES
    \* maxBal[a]: the last ballot the acceptor a \in Acceptor has voted for
    maxBal,
    \* <<maxVBal[a], maxVVal[a]>> is the vote with the largest ballot cast by acceptor a \in Acceptor.
    \* It equals <<-1, None>> if a \in Acceptor has not cast any vote.
    maxVBal, maxVVal, 
    msgs,    \* the set of all messages that have been sent
    ops      \* <<+>> ops[b]: the CAS operation to be proposed at ballot b \in Ballot

vars == <<maxBal, maxVBal, maxVVal, msgs, ops>>
----------------------------------------------------------------------------
TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message
          /\ ops \in [Ballot -> CASOperation] \* <<+>>
----------------------------------------------------------------------------
Init == /\ maxBal  = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVVal = [a \in Acceptor |-> None]
        /\ msgs = {}
        \* <<+>> ops remains unchanged; we utilize TLC to explore all possible CAS operations.
        /\ ops \in [Ballot -> CASOperation]
----------------------------------------------------------------------------
Send(m) == msgs' = msgs \cup {m}
----------------------------------------------------------------------------
(*
The leader of ballot b \in Ballot sends a Phase1a message.
*)
Phase1a(b) == 
    /\ Send([type |-> "1a", bal |-> b])
    /\ ~ \E m \in msgs: /\ m.type = "1a"
                        /\ m.bal = b 
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, ops>>
(*
The acceptor a \in Acceptor receives a Phase1a message
and sends back a Phase1b message.

For refinement:
This action implements the IncreaseMaxBal(a,b) action of the Voting algorithm for b = m.bal.
*)
Phase1b(a) == 
  /\ \E m \in msgs : 
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal])
  /\ UNCHANGED <<maxVBal, maxVVal, ops>>
  
Phase2a(b) ==
  /\ Send([type |-> "2a", bal |-> b])
  /\ \E Q \in Quorum:
        \A a \in Q: \E m \in msgs: /\ m.type = "1b"
                                   /\ m.bal = b
                                   /\ m.acc = a
  /\ UNCHANGED <<maxBal, maxVBal, maxVVal, ops>>
  
Phase2b(a) ==
  /\ \E m \in msgs:
        /\ m.type = "2a"
        /\ m.bal >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal] 
        /\ Send([type |-> "2b", acc|-> a, bal |-> m.bal, mval |-> maxVVal[a], mbal |-> maxVBal[a]])
  /\ UNCHANGED <<maxVBal, maxVVal, ops>>
         
(*
In the Phase3a(b, v) action, the ballot b leader sends a type "2a" message
asking the acceptors to vote for some value computed based on v in ballot number b.

For refinement:
the enabling conditions of the action--its first two conjuncts--ensure that
the second through fourth conjuncts of the four enabling conditions of action VoteFor(a, b, v) in
module Voting will be true when acceptor a receives that message.      
*)
Phase3a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "3a" /\ m.bal = b
  /\ \E Q \in Quorum :
        LET Q2b == {m \in msgs : /\ m.type = "2b"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
            Q2bv == {m \in Q2b : m.mbal >= 0}
        IN  /\ \A a \in Q : \E m \in Q2b : m.acc = a 
            /\ \/ /\ Q2bv = {}  \* <<+>> CAS(None, v) as an initialization operation
                  /\ ops[b].cmpVal = None  \* <<+>>
               \/ /\ \A a \in Q : \E m \in Q2bv : m.acc = a \* a quorum has value v
                  /\ \E m \in Q2bv :  \* <<+>> CAS(v, ops[b].swapVal) as an atomic compare-and-swap operation
                     /\ m.mval = v
                     /\ \A mm \in Q2bv : m.mbal = mm.mbal \* value v comes from same ballot
                     /\ ops[b].cmpVal = v  \* <<+>> not all CAS operations will terminate due to this precondition
  /\ Send([type |-> "3a", bal |-> b, val |-> ops[b].swapVal])  \* <<+>> val |-> ops[b].swapVal
  /\ UNCHANGED <<maxBal, maxVBal, maxVVal, ops>>
(*
The Phase2b(a) action describes what a \in Acceptor does
when it receives a phase 2a message m \in msgs,
which is sent by the leader of ballot m.bal       
asking acceptors to vote for m.val in that ballot.

For refinement:
The enabling condition of the Phase2b(a) action
together with the receipt of the phase 2a message m   
implies that the VoteFor(a, m.bal, m.val) action of module Voting is enabled and can be executed.
*)
Phase3b(a) == 
  /\ \E m \in msgs : 
        /\ m.type = "3a"
        /\ m.bal >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal] 
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal] 
        /\ maxVVal' = [maxVVal EXCEPT ![a] = m.val]
        /\ Send([type |-> "3b", acc |-> a, bal |-> m.bal, val |-> m.val]) 
  /\ UNCHANGED <<ops>>
(*
<<+>> The leader of ballot b \in Ballot responds to the user.
*)
Respond(b) ==
  /\ ~ \E m \in msgs : m.type = "response" /\ m.bal = b
  /\ \E Q \in Quorum : 
\*                       \A a \in Q: \E m \in msgs: /\ m.type = "2b"
\*                                                  /\ m.acc = a
\*                                                  /\ m.bal = b
        LET Q3b == {m \in msgs : /\ m.type = "3b"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
        IN  \A a \in Q : \E m \in Q3b : m.acc = a 
  /\ Send([type |-> "response", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVVal, ops>>
----------------------------------------------------------------------------
Next ==
  \/ \E b \in Ballot :
       \/ Phase1a(b)
       \/ Phase2a(b)
       \/ \E v \in Value : Phase3a(b, v)
       \/ Respond(b) \* <<+>>
  \/ \E a \in Acceptor :
       \/ Phase1b(a)
       \/ Phase2b(a)
       \/ Phase3b(a)

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Sun Sep 18 17:06:45 CST 2022 by 875
\* Created Sun Sep 18 11:53:18 CST 2022 by 875
