--------------------------- MODULE CassandraPaxos ---------------------------
EXTENDS Integers

Maximum(S) == 
  (*************************************************************************)
  (* If S is a set of numbers, then this define Maximum(S) to be the       *)
  (* maximum of those numbers, or -1 if S is empty.                        *)
  (*************************************************************************)
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n \geq m

CONSTANTS Value, Acceptor, Quorum
ASSUME  /\ \A Q \in Quorum : Q \subseteq Acceptor
        /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 /= {}
        
Ballot == Nat

None == CHOOSE v : v \notin Value

Message == 
       [type : {"Prepare"}, bal : Ballot]
  \cup [type : {"Promise"}, acc : Acceptor, bal : Ballot, 
        maxAccBal : Ballot \cup {-1}, maxAccVal : Value \cup {None},
        macComBal : Ballot \cup {-1}, maxComVal : Value \cup {None}]
  \cup [type : {"Propose"}, bal : Ballot, val : Value]
  \cup [type : {"Accept"}, acc : Acceptor, bal : Ballot, val : Value]
  \cup [type : {"Commit"}, bal: Ballot, val: Value]
  \cup [type : {"Ack"}, acc : Acceptor, bal : Ballot,val : Value]

VARIABLES maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, msgs  
vars == <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, msgs>>

TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxAccBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxAccVal  \in [Acceptor -> Value \cup {None}]
          /\ maxComBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxComVal  \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message
                             
          
Init == /\ maxBal  = [a \in Acceptor |-> -1]
        /\ maxAccBal = [a \in Acceptor |-> -1]
        /\ maxAccVal  = [a \in Acceptor |-> None]
        /\ maxComBal = [a \in Acceptor |-> -1]
        /\ maxComVal  = [a \in Acceptor |-> None]
        /\ msgs = {}
        
Send(m) == msgs' = msgs \cup {m}


Prepare(b) == /\ Send([type |-> "Prepare", bal |-> b])
              /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, 
                           maxComVal>>
              
Promise(a) == 
  /\ \E m \in msgs : 
        /\ m.type = "Prepare"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "Promise", acc |-> a, bal |-> m.bal, 
                  maxAccBal |-> maxAccBal[a], maxAccVal |-> maxAccVal[a],
                  maxComBal |-> maxComBal[a], maxComVal |-> maxComVal[a]])
  /\ UNCHANGED <<maxAccBal, maxAccVal, maxComBal, maxComVal>>

  
Propose(b,v) == /\ ~ \E m \in msgs: m.type = "Propose" /\ m.bal = b
                /\ \E Q \in Quorum :
                    LET Qmset == {m \in msgs : /\ m.type = "Promise"
                                               /\ m.acc \in Q
                                               /\ m.bal = b}
                        maxAbal == Maximum({m.maxAccBal : m \in Qmset})
                        maxCbal == Maximum({m.maxComBal : m \in Qmset})
                        val == IF maxAbal > maxCbal 
                                  THEN (CHOOSE m \in Qmset : m.maxAccBal = maxAbal).maxAccVal
                                  ELSE v
                    IN  /\ \A a \in Q : \E m \in Qmset : m.acc = a              
                        /\ Send([type |-> "Propose",bal |-> b, val |-> val])
                /\ UNCHANGED<<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal>>
            
                                                

Accept(a) == /\ \E m \in msgs: /\ m.type="Propose"
                               /\ maxBal[a] \leq m.bal
                               /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                               /\ maxAccBal' = [maxAccBal EXCEPT ![a] = m.bal]
                               /\ maxAccVal' = [maxAccVal EXCEPT ![a] = m.val]
                               /\ Send([type |-> "Accept", bal |-> m.bal, val |-> m.val, 
                                        acc |->a])
            /\ UNCHANGED<<maxComBal, maxComVal>>    

             
Commit(b,v) == /\ ~\E m \in msgs : m.type = "Commit" /\ m.bal = b
               /\ \E Q \in Quorum :
                   LET QAmset == {m \in msgs : /\ m.type="Accept"
                                             /\ m.acc \in Q
                                             /\ m.bal=b}
                   IN /\ \A a \in Q : \E m \in QAmset : m.acc = a
               /\ Send([type |-> "Commit", bal |-> b, val |-> v])
               /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, 
                             maxComVal>>
               
Ack(a) == /\ \E m \in msgs: /\ m.type="Commit"
                            /\ maxBal[a] \leq m.bal
                            /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                            /\ maxComBal' = [maxComBal EXCEPT ![a] = m.bal]
                            /\ maxComVal' = [maxComVal EXCEPT ![a] = m.val]
                            /\ Send([type |-> "Ack", bal |-> m.bal, val |-> m.val, 
                                    acc |->a])
          /\ UNCHANGED<<maxAccBal, maxAccVal>>


Next == \/ \E b \in Ballot : \/ Prepare(b) 
                             \/ \E v \in Value: Propose(b,v) \/ Commit(b,v)
        \/ \E a \in Acceptor : \/ Promise(a) \/ Accept(a) \/ Ack(a)

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Thu Dec 09 19:33:06 CST 2021 by LENOVO
\* Created Thu Dec 02 10:19:29 CST 2021 by LENOVO
