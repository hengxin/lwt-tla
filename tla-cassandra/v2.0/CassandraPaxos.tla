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


CONSTANTS Value, Acceptor, Quorum, Precondition

ASSUME  /\ \A Q \in Quorum : Q \subseteq Acceptor
        /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 /= {}
        
Ballot == Nat

None == CHOOSE v : v \notin Value

MeetCondition(val) == IF val # None THEN 
  (*************************************************************************)
  (* If condition is satisfied,then TRUE                                *)                                
  (*************************************************************************)
               CASE  Precondition.operator=">" -> val  >  Precondition.value
                  [] Precondition.operator="<" -> val  <  Precondition.value
                  [] Precondition.operator="=" -> val  =  Precondition.value
                  [] Precondition.operator=">=" -> val >= Precondition.value
                  [] Precondition.operator="<=" -> val <= Precondition.value
                  [] Precondition.operator="/=" -> val /= Precondition.value
                  [] OTHER -> FALSE
            ELSE TRUE 

Message == 
       [type : {"Prepare"}, bal : Ballot]
  \cup [type : {"Promise"}, acc : Acceptor, bal : Ballot, 
        maxAccBal : Ballot \cup {-1}, maxAccVal : Value \cup {None},
        maxComBal : Ballot \cup {-1}, maxComVal : Value \cup {None}]
  \cup [type : {"Read"}, bal : Ballot]
  \cup [type : {"Result"}, bal : Ballot, acc : Acceptor,
                result : Value \cup {None}, version: Nat ]
  \cup [type : {"Repair"}, result : Value \cup {None}, version: Nat]
  \cup [type : {"Propose"}, bal : Ballot, val : Value]
  \cup [type : {"Accept"}, acc : Acceptor, bal : Ballot, val : Value]
  \cup [type : {"Commit"}, bal: Ballot, val: Value]
  \cup [type : {"Ack"}, acc : Acceptor, bal : Ballot,val : Value]
  \cup [type : {"Terminate"}, bal : Ballot]

VARIABLES maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, msgs, dataResult  
vars == <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, msgs, dataResult>>

TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxAccBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxAccVal  \in [Acceptor -> Value \cup {None}]
          /\ maxComBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxComVal  \in [Acceptor -> Value \cup {None}]
          /\ dataResult  \in [Acceptor -> [result : Value \cup {None}, version : Nat]]
          /\ msgs \subseteq Message               
          
Init == /\ maxBal  = [a \in Acceptor |-> -1]
        /\ maxAccBal = [a \in Acceptor |-> -1]
        /\ maxAccVal  = [a \in Acceptor |-> None]
        /\ maxComBal = [a \in Acceptor |-> -1]
        /\ maxComVal  = [a \in Acceptor |-> None]
        /\ dataResult = [a \in Acceptor |-> [result |-> None, version  |-> 0]]
        /\ msgs = {}
        
Send(m) == msgs' = msgs \cup {m}


Prepare(b) == /\ Send([type |-> "Prepare", bal |-> b])
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
        
  /\ UNCHANGED <<maxAccBal, maxAccVal, maxComBal, maxComVal, dataResult>>

  
Propose(b,v) == /\ ~ \E m \in msgs: m.type = "Propose" /\ m.bal = b
                /\ \E Q \in Quorum :
                    LET Qmset == {m \in msgs : /\ m.type = "Promise"
                                               /\ m.acc \in Q
                                               /\ m.bal = b}
                        maxAccbal == Maximum({m.maxAccBal : m \in Qmset})
                        maxCombal == Maximum({m.maxComBal : m \in Qmset})
                        (**If there is an uncommitted submission, propose the uncommitted value first**)
                        (**If you can propose your own value, you need to read to get this value**)
                        value == IF maxAccbal > maxCombal 
                                     THEN (CHOOSE m \in Qmset : m.maxAccBal = maxAccbal).maxAccVal
                                     ELSE v
                        Qmsetv == {m \in Qmset : m.maxAccBal >= 0}
                    IN  /\ \A a \in Q : \E m \in Qmset : m.acc = a
                        /\ \/ Qmsetv = {}
                           \/ \E m \in Qmsetv : /\ m.maxAccVal = v
                                                /\ \A mm \in Qmsetv : m.maxAccBal >= mm.maxAccBal            
                        /\ IF value=v  THEN Send([type |-> "Read", bal |-> b])
                                       ELSE Send([type |-> "Propose", bal |-> b, val |-> v])
                /\ UNCHANGED<<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, dataResult>>
            
            
Read(a) == /\ \E m \in msgs : /\ m.type = "Read" 
                              /\ Send([type |-> "Result", acc |-> a, bal |->m.bal,
                                       result |-> dataResult[a].result, 
                                       version |-> dataResult[a].version])
             /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal,
                            dataResult>>
                          
Result(b,v) == /\ \E Q \in Quorum : 
                  LET QRmset == {m \in msgs : /\ m.type = "Result"
                                              /\ m.acc \in Q
                                              /\ m.bal = b }
                      QResult == {m.result : m \in QRmset}
                      res == IF Same(QResult) THEN CHOOSE n \in QResult : \A m \in QResult : n=m
                                              ELSE -1
                      ver == Maximum({m.version : m \in QRmset})
                      res2 == (CHOOSE m \in QRmset : m.version=ver).result
                  IN  /\ \A a \in Q : \E m \in QRmset : m.acc = a 
                      /\ IF res=-1 THEN Send([type |-> "Repair", result |-> res2, version |-> ver])
                                   ELSE (IF MeetCondition(res) THEN Send([type |-> "Propose", bal |-> b, val |-> v])    
                                                                ELSE Send([type |-> "Terminate", bal |->b])
                                        )
                                                             
               /\ UNCHANGED<<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, dataResult>>
                                          

                                                      
Repair(a) == /\ \E m \in msgs: /\ m.type="Repair"
                               /\ dataResult' = [dataResult EXCEPT ![a] =
                                                   [result |-> m.result, version |-> m.version]]
             /\ UNCHANGED<<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, msgs>>

         

Accept(a) == /\ \E m \in msgs: /\ m.type="Propose"
                               /\ maxBal[a] \leq m.bal
                               /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                               /\ maxAccBal' = [maxAccBal EXCEPT ![a] = m.bal]
                               /\ maxAccVal' = [maxAccVal EXCEPT ![a] = m.val]
                               /\ Send([type |-> "Accept", bal |-> m.bal, val |-> m.val, 
                                       acc |->a])
             /\ UNCHANGED<<maxComBal, maxComVal, dataResult>>    

             
Commit(b,v) == /\ ~\E m \in msgs : m.type = "Commit" /\ m.bal = b
               /\ \E Q \in Quorum :
                   LET QAmset == {m \in msgs : /\ m.type="Accept"
                                               /\ m.acc \in Q
                                               /\ m.bal=b}
                   IN /\ \A a \in Q : \E m \in QAmset : m.acc = a
               /\ Send([type |-> "Commit", bal |-> b, val |-> v])
               /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, 
                              maxComVal, dataResult>>
               
Ack(a) == /\ \E m \in msgs: /\ m.type="Commit"
                            /\ maxBal[a] \leq m.bal
                            /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                            /\ maxComBal' = [maxComBal EXCEPT ![a] = m.bal]
                            /\ maxComVal' = [maxComVal EXCEPT ![a] = m.val]
                            /\ dataResult' = [dataResult EXCEPT ![a]=
                                [result|-> m.val, version |->(@.version+1)] ]
                            /\ Send([type |-> "Ack", bal |-> m.bal, val |-> m.val, 
                                    acc |->a])
          \*/\UNCHANGED<<maxAccBal, maxAccVal, dataResult>>
          /\UNCHANGED<<maxAccBal, maxAccVal>>


Next == \/ \E b \in Ballot : \/ Prepare(b) 
                             \/ \E v \in Value : \/ Propose(b,v) 
                                                 \/ Result(b,v)
                                                 \/ Commit(b,v)
        \/ \E a \in Acceptor : \/ Promise(a) 
                               \/ Accept(a) 
                               \/ Ack(a)
                               \/ Read(a)
                               \/ Repair(a)                          
              
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
\* Last modified Tue Dec 28 11:39:38 CST 2021 by LENOVO
\* Created Thu Dec 08 10:19:29 CST 2021 by LENOVO
