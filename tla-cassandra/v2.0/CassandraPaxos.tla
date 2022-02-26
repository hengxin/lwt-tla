--------------------------- MODULE CassandraPaxos ---------------------------
EXTENDS Integers

Maximum(S) == 
  (*************************************************************************)
  (* If S is a set of numbers, then this define Maximum(S) to be the       *)
  (* maximum of those numbers, or -1 if S is empty.                        *)
  (*************************************************************************)
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n \geq m
 
Same(S) ==
  (*************************************************************************)
  (* If S is not empty, then this define Same(S) to be the                 *)
  (* if or not the element of S is same.                                   *)
  (* It is designed for determine whether the results of Read are the same *)
  (*************************************************************************)
  /\ S # {}
  /\  \E n \in S: \A m \in S : n = m          

CONSTANTS Value, Acceptor, Quorum, Operator

ASSUME  /\ \A Q \in Quorum : Q \subseteq Acceptor
        /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 /= {}
        
Ballot == Nat
Version == Nat
None == CHOOSE v : v \notin Value

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
  \cup [type : {"Result"}, bal : Ballot, acc : Acceptor,
                value : Value \cup {None}, version: Version ]
  \cup [type : {"Repair"}, value : Value \cup {None}, version: Version]
  \cup [type : {"Propose"}, bal : Ballot, val : Value]
  \cup [type : {"Accept"}, acc : Acceptor, bal : Ballot, val : Value]
  \cup [type : {"Commit"}, bal: Ballot, val: Value]
  \cup [type : {"Ack"}, acc : Acceptor, bal : Ballot,val : Value]
  \cup [type : {"Terminate"}, bal : Ballot]

VARIABLES maxBal, maxAccBal, maxAccVal, maxComBal, 
          maxComVal, msgs, dataResult, balValue  
vars == <<maxBal, maxAccBal, maxAccVal, maxComBal, 
          maxComVal, msgs, dataResult, balValue>>

TypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxAccBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxAccVal \in [Acceptor -> Value \cup {None}]
          /\ maxComBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxComVal \in [Acceptor -> Value \cup {None}]
          /\ dataResult \in [Acceptor -> [value : Value \cup {None}, 
                                           version : Version]]
          /\ msgs \subseteq Message 
          /\ balValue \in [Ballot -> [expVal : Value \cup {None},
                                      setVal : Value \cup {None}]]               
          
Init == /\ maxBal  = [a \in Acceptor |-> -1]
        /\ maxAccBal = [a \in Acceptor |-> -1]
        /\ maxAccVal  = [a \in Acceptor |-> None]
        /\ maxComBal = [a \in Acceptor |-> -1]
        /\ maxComVal  = [a \in Acceptor |-> None]
        /\ dataResult = [a \in Acceptor |-> [value |-> None, version  |-> 0]]
        /\ msgs = {}
        /\ balValue = [b \in Ballot |->[expVal |-> None, setVal |-> None]]
        
        
Send(m) == msgs' = msgs \cup {m}
 
CAS(ev,sv,b) ==  /\ ~ \E m \in msgs: m.type = "Prepare" /\ m.bal = b 
                 /\ Send([type |-> "Prepare", bal |-> b])
                 /\ balValue' = [balValue EXCEPT ![b]=
                                 [expVal |-> ev, setVal |-> sv]]
                 /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, 
                           maxComVal, dataResult>>        
                           
Promise(a) == 
  /\ \E m \in msgs : 
        /\ m.type = "Prepare"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "Promise", acc |-> a, bal |-> m.bal, 
                  maxAccBal |-> maxAccBal[a], maxAccVal |-> maxAccVal[a],
                  maxComBal |-> maxComBal[a], maxComVal |-> maxComVal[a]
                ])
        
  /\ UNCHANGED <<maxAccBal, maxAccVal, maxComBal, maxComVal, 
                dataResult, balValue>>

  
Propose(b) == /\ ~ \E m \in msgs: m.type = "Propose" /\ m.bal = b
              /\ \E Q \in Quorum :
                  LET Qmset == {m \in msgs : /\ m.type = "Promise"
                                             /\ m.acc \in Q
                                             /\ m.bal = b}
                      maxAccbal == Maximum({m.maxAccBal : m \in Qmset})
                      maxCombal == Maximum({m.maxComBal : m \in Qmset})
                      preValue == (CHOOSE m \in Qmset : m.maxAccBal = maxAccbal).maxAccVal
                  IN  /\ \A a \in Q : \E m \in Qmset : m.acc = a   
                      /\ IF maxAccbal > maxCombal  THEN Send([type |-> "Propose",
                                                             bal |-> b, val |-> preValue])
                                                   ELSE Send([type |-> "Read", bal |-> b])
              /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, 
                              dataResult, balValue>>
            
            
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
                    maxVersion == Maximum({m.version : m \in QRmset}) 
                    maxValue == (CHOOSE m \in QRmset : m.version=maxVersion).value 
                IN  /\ \A a \in Q : \E m \in QRmset : m.acc = a 
                    /\ IF MeetCondition(balValue[b].expVal,maxValue) 
                            THEN Send([type |-> "Propose", bal |-> b, 
                                      val |-> balValue[b].setVal])
                            ELSE Send([type |-> "Terminate", bal |->b])
                      
                      \*/\ IF ~Same(QResult) THEN Send([type |-> "Repair", 
                      \*                               value |-> maxValue, 
                      \*                               version |-> maxVersion])
                  /\ UNCHANGED<<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, 
                                dataResult, balValue>>                

(************************************************************************************                                                     
Repair(a) == /\ \E m \in msgs: /\ m.type="Repair"
                               /\ dataResult' = [dataResult EXCEPT ![a] =
                                                   [value |-> m.value, 
                                                   version |-> m.version]]
             /\ UNCHANGED<<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, 
                           msgs, balValue>>
************************************************************************************)
         

Accept(a) == /\ \E m \in msgs: /\ m.type="Propose"
                               /\ maxBal[a] \leq m.bal
                               /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                               /\ maxAccBal' = [maxAccBal EXCEPT ![a] = m.bal]
                               /\ maxAccVal' = [maxAccVal EXCEPT ![a] = m.val]
                               /\ Send([type |-> "Accept", bal |-> m.bal,
                                       val |-> m.val, acc |->a])
             /\ UNCHANGED<<maxComBal, maxComVal, dataResult, balValue>>    

             
Commit(b) == /\ ~\E m \in msgs : m.type = "Commit" /\ m.bal = b
             /\ \E Q \in Quorum :
                 LET QAmset == {m \in msgs : /\ m.type="Accept"
                                             /\ m.acc \in Q
                                             /\ m.bal=b}
                 IN /\ \A a \in Q : \E m \in QAmset : m.acc = a
             /\ Send([type |-> "Commit", bal |-> b, 
                     val |-> balValue[b].setVal])
             /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, 
                            maxComVal, dataResult, balValue>>
               
Ack(a) == /\ \E m \in msgs: /\ m.type="Commit"
                            /\ maxBal[a] \leq m.bal
                            /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                            /\ maxComBal' = [maxComBal EXCEPT ![a] = m.bal]
                            /\ maxComVal' = [maxComVal EXCEPT ![a] = m.val]
                            \*/\ dataResult' = [dataResult EXCEPT ![a]=
                               \*[value |-> m.val, version |->(@.version+1)]]
                            /\ Send([type |-> "Ack", bal |-> m.bal, 
                                    val |-> m.val, acc |->a])
          \*/\UNCHANGED <<maxAccBal, maxAccVal, balValue>>
          /\UNCHANGED <<maxAccBal, maxAccVal, dataResult, balValue>>
                    
Next == \/ \E ev, sv \in Value, b \in Ballot : CAS(ev,sv,b)
        \/ \E b \in Ballot : \/ Propose(b)
                             \/ Result(b)
                             \/ Commit(b)
        \/ \E a \in Acceptor : \/ Promise(a)
                               \/ Accept(a)
                               \/ Ack(a)
                               \/ Read(a)                         
              
Spec == Init /\ [][Next]_vars

votes == 
  [a \in Acceptor |->  
      {<<m.bal, m.val>> : m \in {mm \in msgs: /\ mm.type = "Ack"
                                              /\ mm.acc = a }}]
                                              
V == INSTANCE Voting

Inv == 
 /\ TypeOK
 /\ \A a \in Acceptor: /\ maxBal[a] >= maxAccBal[a]
                       /\ maxBal[a] >= maxComBal[a]
 /\ \A a \in Acceptor : IF maxComBal[a] = -1
                          THEN maxComVal[a] = None
                          ELSE <<maxComBal[a], maxComVal[a]>> \in votes[a]
                                                         
=============================================================================
\* Modification History
\* Last modified Fri Feb 25 18:54:47 CST 2022 by LENOVO
\* Created Thu Dec 08 10:19:29 CST 2021 by LENOVO