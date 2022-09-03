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
    Operator,   \* TODO
    Ballot,
    Version

None == CHOOSE v : v \notin Value 

ASSUME  /\ \A Q \in Quorum : Q \subseteq Acceptor
        /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
-----------------------------------------------------------------------------
(*
<<+>> The set of all possible CAS operations.
The CAS operations with cmpVal = None are initialization operations.
We assume that the new values (i.e., swapVal) are not None.
*)
CASOperation == [cmpVal : Value, swapVal : Value]

MeetCondition(ev,val) == \/ val = None  
                         \/ CASE  Operator=">" -> val  >  ev
                               [] Operator="<" -> val  <  ev
                               [] Operator="=" -> val  =  ev
                               [] Operator=">=" -> val >= ev
                               [] Operator="<=" -> val <= ev
                               [] Operator="/=" -> val /= ev
                               [] OTHER -> FALSE
Message == 
       [type : {"1a"}, bal : Ballot]
  \cup [type : {"1b"}, acc : Acceptor, bal : Ballot, 
        maxAccBal : Ballot \cup {-1}, maxAccVal : Value \cup {None},
        maxComBal : Ballot \cup {-1}, maxComVal : Value \cup {None}]
  \cup [type : {"2a"}, bal : Ballot]
  \cup [type : {"2b"}, acc : Acceptor, bal : Ballot,
                value : Value \cup {None}, version: Version]
  \cup [type : {"Repair"}, value : Value \cup {None}, version: Version]
  \cup [type : {"3a"}, bal : Ballot, val : Value]
  \cup [type : {"3b"}, acc : Acceptor, bal : Ballot, val : Value]
  \cup [type : {"4a"}, bal: Ballot, val: Value]
  \cup [type : {"4b"}, acc : Acceptor, bal : Ballot,val : Value]
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
    ops         \* <<+>> ops[b]: the CAS operation to be proposed at ballot b \in Ballot

vars == <<maxBal, maxAccBal, maxAccVal, maxComBal, 
          maxComVal, msgs, dataResult, ops>>
-----------------------------------------------------------------------------
TypeOK ==
    /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxAccBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxAccVal \in [Acceptor -> Value \cup {None}]
    /\ maxComBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxComVal \in [Acceptor -> Value \cup {None}]
    /\ msgs \subseteq Message 
    /\ dataResult \in [Acceptor -> [value : Value \cup {None}, version : Version]]      
    /\ ops \in [Ballot -> CASOperation] \* <<+>>
-----------------------------------------------------------------------------
Init == /\ maxBal  = [a \in Acceptor |-> -1]
        /\ maxAccBal = [a \in Acceptor |-> -1]
        /\ maxAccVal  = [a \in Acceptor |-> None]
        /\ maxComBal = [a \in Acceptor |-> -1]
        /\ maxComVal  = [a \in Acceptor |-> None]
        /\ msgs = {}
        /\ dataResult = [a \in Acceptor |-> [value |-> None, version  |-> 0]]
        \* <<+>> ops remains  unchanged; we utilize TLC to explore all possible CAS operations.
        /\ ops \in [Ballot -> CASOperation]
-----------------------------------------------------------------------------
Send(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
(*
The leader of ballot b \in Ballot sends a "Prepare" message.
*)
Phase1a(b) ==
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, dataResult, ops>>        
(*
The acceptor a \in Acceptor receives a "Prepare" message and sends back a "Promise" message.
*)                           
Phase1b(a) == 
  /\ \E m \in msgs : 
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, 
                  maxAccBal |-> maxAccBal[a], maxAccVal |-> maxAccVal[a],
                  maxComBal |-> maxComBal[a], maxComVal |-> maxComVal[a]])
  /\ UNCHANGED <<maxAccBal, maxAccVal, maxComBal, maxComVal, 
                dataResult, ops>>
-----------------------------------------------------------------------------
Phase2a(b) ==
    /\ ~ \E m \in msgs: m.type = "3a" /\ m.bal = b
    /\ \E Q \in Quorum :
        LET Qmset == {m \in msgs : /\ m.type = "1b"
                                   /\ m.acc \in Q
                                   /\ m.bal = b}
            maxAccbal == Max({m.maxAccBal : m \in Qmset})
            maxCombal == Max({m.maxComBal : m \in Qmset})
            preValue == (CHOOSE m \in Qmset : m.maxAccBal = maxAccbal).maxAccVal
        IN  /\ \A a \in Q : \E m \in Qmset : m.acc = a   
            /\ IF maxAccbal > maxCombal  THEN Send([type |-> "3a",
                                                   bal |-> b, val |-> preValue])
                                         ELSE Send([type |-> "2a", bal |-> b])
    /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, 
                   dataResult, ops>>
            
            
Phase2b(a) == /\ \E m \in msgs : /\ m.type = "2a" 
                              /\ Send([type |-> "2b", acc |-> a, bal |->m.bal,
                                       value |-> dataResult[a].value, 
                                       version |-> dataResult[a].version])
           /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal,
                            dataResult, ops>>
                          
Phase3a(b) == /\ ~ \E m \in msgs: m.type = "Terminate" /\ m.bal = b
              /\ \E Q \in Quorum : 
                LET QRmset == {m \in msgs : /\ m.type = "2b"
                                            /\ m.acc \in Q
                                            /\ m.bal = b }
                    QResult == {m.value : m \in QRmset}
                    maxVersion == Max({m.version : m \in QRmset}) 
                    maxValue == (CHOOSE m \in QRmset : m.version=maxVersion).value 
                IN  /\ \A a \in Q : \E m \in QRmset : m.acc = a 
                    /\ IF MeetCondition(ops[b].cmpVal,maxValue) 
                            THEN Send([type |-> "3a", bal |-> b, 
                                      val |-> ops[b].swapVal])
                            ELSE Send([type |-> "Terminate", bal |->b])
                    /\ UNCHANGED<<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, 
                                dataResult, ops>>                

Phase3b(a) == /\ \E m \in msgs: /\ m.type="3a"
                               /\ maxBal[a] = m.bal
                               \*/\ maxBal[a] \leq m.bal
                               \*/\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                               /\ maxAccBal' = [maxAccBal EXCEPT ![a] = m.bal]
                               /\ maxAccVal' = [maxAccVal EXCEPT ![a] = m.val]
                               /\ Send([type |-> "3b", bal |-> m.bal,
                                       val |-> m.val, acc |->a])
             \*/\ UNCHANGED<<maxComBal, maxComVal, dataResult, balValue>>   
             /\ UNCHANGED<<maxBal, maxComBal, maxComVal, dataResult, ops>>  

             
Phase4a(b) == /\ ~\E m \in msgs : m.type = "4a" /\ m.bal = b
             /\ \E Q \in Quorum :
                 LET QAmset == {m \in msgs : /\ m.type="3b"
                                             /\ m.acc \in Q
                                             /\ m.bal=b}
                 IN /\ \A a \in Q : \E m \in QAmset : m.acc = a
             /\ Send([type |-> "4a", bal |-> b, 
                     val |-> ops[b].swapVal])
             /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, 
                            maxComVal, dataResult, ops>>
               
Phase4b(a) == /\ \E m \in msgs: /\ m.type="4a"
                            \*/\ maxBal[a] \leq m.bal
                            \*/\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                            /\ maxBal[a] = m.bal
                            /\ maxComBal' = [maxComBal EXCEPT ![a] = m.bal]
                            /\ maxComVal' = [maxComVal EXCEPT ![a] = m.val]
                            \*/\ dataResult' = [dataResult EXCEPT ![a]=
                               \*[value |-> m.val, version |->(@.version+1)]]
                            /\ Send([type |-> "4b", bal |-> m.bal, 
                                    val |-> m.val, acc |->a])
          \*/\UNCHANGED <<maxAccBal, maxAccVal, balValue>>
          \*/\UNCHANGED <<maxAccBal, maxAccVal, dataResult, balValue>> 
          /\UNCHANGED <<maxBal, maxAccBal, maxAccVal, dataResult, ops>>
-----------------------------------------------------------------------------
Next ==
    \/ \E ev, sv \in Value, b \in Ballot : Phase1a(b)
    \/ \E b \in Ballot : \/ Phase2a(b)
                         \/ Phase3a(b)
                         \/ Phase4a(b)
    \/ \E a \in Acceptor : \/ Phase1b(a)
                           \/ Phase3b(a)
                           \/ Phase4b(a)
                           \/ Phase2b(a)
              
Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Fri Sep 02 13:40:07 CST 2022 by 875
\* Last modified Sat Aug 20 13:41:52 CST 2022 by hengxin
\* Last modified Thu Mar 03 17:37:19 CST 2022 by LENOVO
\* Created Thu Dec 08 10:19:29 CST 2021 by LENOVO