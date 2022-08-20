--------------------------- MODULE CassandraPaxos ---------------------------
(*
This is a high-level specification of the CassandraPaxos algorithm
used by Cassandra to implement LWT (lightweight transactions).

This spec is adapted from that of Paxos consensus algorithm by Leslie Lamport,
which can be found at https://github.com/tlaplus/Examples/blob/master/specifications/PaxosHowToWinATuringAward/Paxos.tla.
*)
EXTENDS Integers, Sequences, FiniteSets
-----------------------------------------------------------------------------
Max(S) == 
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n \geq m
-----------------------------------------------------------------------------
CONSTANTS
    Value,      \* the set of values to be proposed and chosen from
    Acceptor,   \* the set acceptors
    Quorum,     \* the quorum system on acceptors
    Operator    \* TODO

None == CHOOSE v : v \notin Value 

ASSUME  /\ \A Q \in Quorum : Q \subseteq Acceptor
        /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
-----------------------------------------------------------------------------
Ballot == Nat
Version == Nat  \* TODO

(*
<<+>> The set of all possible CAS operations.
The CAS operations with cmpVal = None are initialization operations.
We assume that the new values (i.e., swapVal) are not None.
*)
CASOperation == [cmpVal : Value \cup {None}, swapVal : Value]

MeetCondition(ev,val) == \/ val = None  
                         \/ CASE  Operator=">" -> val  >  ev
                               [] Operator="<" -> val  <  ev
                               [] Operator="=" -> val  =  ev
                               [] Operator=">=" -> val >= ev
                               [] Operator="<=" -> val <= ev
                               [] Operator="/=" -> val /= ev
                               [] OTHER -> FALSE
Message == 
       [type : {"Prepare"}, bal : Ballot]
  \cup [type : {"Promise"}, acc : Acceptor, bal : Ballot, 
        maxAccBal : Ballot \cup {-1}, maxAccVal : Value \cup {None},
        maxComBal : Ballot \cup {-1}, maxComVal : Value \cup {None}]
  \cup [type : {"Read"}, bal : Ballot]
  \cup [type : {"Result"}, acc : Acceptor, bal : Ballot,
                value : Value \cup {None}, version: Version]
  \cup [type : {"Repair"}, value : Value \cup {None}, version: Version]
  \cup [type : {"Propose"}, bal : Ballot, val : Value]
  \cup [type : {"Accept"}, acc : Acceptor, bal : Ballot, val : Value]
  \cup [type : {"Commit"}, bal: Ballot, val: Value]
  \cup [type : {"Ack"}, acc : Acceptor, bal : Ballot,val : Value]
  \cup [type : {"Terminate"}, bal : Ballot] \* <<+>> the messages sent to the user
-----------------------------------------------------------------------------
VARIABLES
    maxBal,
    maxAccBal,
    maxAccVal,
    maxComBal, 
    maxComVal,
    msgs,
    dataResult,
    balValue,   \* TODO: remove it?
    ops         \* <<+>> ops[b]: the CAS operation to be proposed at ballot b \in Ballot

vars == <<maxBal, maxAccBal, maxAccVal, maxComBal, 
          maxComVal, msgs, dataResult, balValue, ops>>
-----------------------------------------------------------------------------
TypeOK ==
    /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxAccBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxAccVal \in [Acceptor -> Value \cup {None}]
    /\ maxComBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxComVal \in [Acceptor -> Value \cup {None}]
    /\ msgs \subseteq Message 
    /\ dataResult \in [Acceptor -> [value : Value \cup {None}, version : Version]]
    /\ balValue \in [Ballot -> [cmpVal : Value \cup {None}, swapVal : Value \cup {None}]]               
    /\ ops \in [Ballot -> CASOperation] \* <<+>>
-----------------------------------------------------------------------------
Init == /\ maxBal  = [a \in Acceptor |-> -1]
        /\ maxAccBal = [a \in Acceptor |-> -1]
        /\ maxAccVal  = [a \in Acceptor |-> None]
        /\ maxComBal = [a \in Acceptor |-> -1]
        /\ maxComVal  = [a \in Acceptor |-> None]
        /\ msgs = {}
        /\ dataResult = [a \in Acceptor |-> [value |-> None, version  |-> 0]]
        /\ balValue = [b \in Ballot |->[cmpVal |-> None, swapVal |-> None]]
        \* <<+>> ops remains  unchanged; we utilize TLC to explore all possible CAS operations.
        /\ ops \in [Ballot -> CASOperation]
-----------------------------------------------------------------------------
Send(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
(*
The leader of ballot b \in Ballot sends a "Prepare" message.
*)
Prepare(b) ==
    /\ Send([type |-> "Prepare", bal |-> b])
    /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, balValue, dataResult, ops>>        
(*
The acceptor a \in Acceptor receives a "Prepare" message and sends back a "Promise" message.
*)                           
Promise(a) == 
  /\ \E m \in msgs : 
        /\ m.type = "Prepare"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "Promise", acc |-> a, bal |-> m.bal, 
                  maxAccBal |-> maxAccBal[a], maxAccVal |-> maxAccVal[a],
                  maxComBal |-> maxComBal[a], maxComVal |-> maxComVal[a]])
  /\ UNCHANGED <<maxAccBal, maxAccVal, maxComBal, maxComVal, 
                dataResult, balValue, ops>>
-----------------------------------------------------------------------------
Propose(b) ==
    /\ ~ \E m \in msgs: m.type = "Propose" /\ m.bal = b
    /\ \E Q \in Quorum :
        LET Qmset == {m \in msgs : /\ m.type = "Promise"
                                   /\ m.acc \in Q
                                   /\ m.bal = b}
            maxAccbal == Max({m.maxAccBal : m \in Qmset})
            maxCombal == Max({m.maxComBal : m \in Qmset})
            preValue == (CHOOSE m \in Qmset : m.maxAccBal = maxAccbal).maxAccVal
        IN  /\ \A a \in Q : \E m \in Qmset : m.acc = a   
            /\ IF maxAccbal > maxCombal  THEN Send([type |-> "Propose",
                                                   bal |-> b, val |-> preValue])
                                         ELSE Send([type |-> "Read", bal |-> b])
    /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, 
                   dataResult, balValue, ops>>
            
            
Read(a) == /\ \E m \in msgs : /\ m.type = "Read" 
                              /\ Send([type |-> "Result", acc |-> a, bal |->m.bal,
                                       value |-> dataResult[a].value, 
                                       version |-> dataResult[a].version])
           /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal,
                            dataResult, balValue>>
                          
Result(b) == /\ \E Q \in Quorum : 
                LET QRmset == {m \in msgs : /\ m.type = "Result"
                                            /\ m.acc \in Q
                                            /\ m.bal = b }
                    QResult == {m.value : m \in QRmset}
                    maxVersion == Max({m.version : m \in QRmset}) 
                    maxValue == (CHOOSE m \in QRmset : m.version=maxVersion).value 
                IN  /\ \A a \in Q : \E m \in QRmset : m.acc = a 
                    /\ IF MeetCondition(balValue[b].cmpVal,maxValue) 
                            THEN Send([type |-> "Propose", bal |-> b, 
                                      val |-> balValue[b].swapVal])
                            ELSE Send([type |-> "Terminate", bal |->b])
                    /\ UNCHANGED<<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, 
                                dataResult, balValue>>                

Accept(a) == /\ \E m \in msgs: /\ m.type="Propose"
                               /\ maxBal[a] = m.bal
                               \*/\ maxBal[a] \leq m.bal
                               \*/\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                               /\ maxAccBal' = [maxAccBal EXCEPT ![a] = m.bal]
                               /\ maxAccVal' = [maxAccVal EXCEPT ![a] = m.val]
                               /\ Send([type |-> "Accept", bal |-> m.bal,
                                       val |-> m.val, acc |->a])
             \*/\ UNCHANGED<<maxComBal, maxComVal, dataResult, balValue>>   
             /\ UNCHANGED<<maxBal, maxComBal, maxComVal, dataResult, balValue>>  

             
Commit(b) == /\ ~\E m \in msgs : m.type = "Commit" /\ m.bal = b
             /\ \E Q \in Quorum :
                 LET QAmset == {m \in msgs : /\ m.type="Accept"
                                             /\ m.acc \in Q
                                             /\ m.bal=b}
                 IN /\ \A a \in Q : \E m \in QAmset : m.acc = a
             /\ Send([type |-> "Commit", bal |-> b, 
                     val |-> balValue[b].swapVal])
             /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, 
                            maxComVal, dataResult, balValue>>
               
Ack(a) == /\ \E m \in msgs: /\ m.type="Commit"
                            \*/\ maxBal[a] \leq m.bal
                            \*/\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                            /\ maxBal[a] = m.bal
                            /\ maxComBal' = [maxComBal EXCEPT ![a] = m.bal]
                            /\ maxComVal' = [maxComVal EXCEPT ![a] = m.val]
                            \*/\ dataResult' = [dataResult EXCEPT ![a]=
                               \*[value |-> m.val, version |->(@.version+1)]]
                            /\ Send([type |-> "Ack", bal |-> m.bal, 
                                    val |-> m.val, acc |->a])
          \*/\UNCHANGED <<maxAccBal, maxAccVal, balValue>>
          \*/\UNCHANGED <<maxAccBal, maxAccVal, dataResult, balValue>> 
          /\UNCHANGED <<maxBal, maxAccBal, maxAccVal, dataResult, balValue>>
-----------------------------------------------------------------------------
Next ==
    \/ \E ev, sv \in Value, b \in Ballot : Prepare(b)
    \/ \E b \in Ballot : \/ Propose(b)
                         \/ Result(b)
                         \/ Commit(b)
    \/ \E a \in Acceptor : \/ Promise(a)
                           \/ Accept(a)
                           \/ Ack(a)
                           \/ Read(a)
              
Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Sat Aug 20 13:41:52 CST 2022 by hengxin
\* Last modified Thu Mar 03 17:37:19 CST 2022 by LENOVO
\* Created Thu Dec 08 10:19:29 CST 2021 by LENOVO