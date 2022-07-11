------------------------------- MODULE ScyllaPaxos -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

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
InitVal == CHOOSE v \in Value : TRUE

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
        maxComBal : Ballot \cup {-1}, maxComVal : Value \cup {None},
        value : Value, version : Version]
  \cup [type : {"Repair"}, value : Value \cup {None}, version: Version]
  \cup [type : {"Propose"}, bal : Ballot, val : Value]
  \cup [type : {"Accept"}, acc : Acceptor, bal : Ballot, val : Value]
  \cup [type : {"Learn"}, bal: Ballot, val: Value]
  \cup [type : {"Ack"}, acc : Acceptor, bal : Ballot,val : Value]
  \cup [type : {"Terminate"}, bal : Ballot]
  
Events == [type : {"invoke", "response"}, bal : Ballot, expVal : Value,
           setVal : Value, flag : {"TRUE","FALSE"} ]

VARIABLES maxBal, maxAccBal, maxAccVal, maxComBal, 
          maxComVal, msgs, balValue, history,dataResult  
vars == <<maxBal, maxAccBal, maxAccVal, maxComBal, 
          maxComVal, msgs, balValue, history,dataResult>>

TypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxAccBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxAccVal \in [Acceptor -> Value ]
          /\ maxComBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxComVal \in [Acceptor -> Value ]
          /\ msgs \subseteq Message 
          /\ balValue \in [Ballot -> [expVal : Value,
                                      setVal : Value]]  
          \*/\ history \in Seq(Events) 
          /\ dataResult \in [Acceptor -> [value : Value, 
                                         version : Version]]            
          
Init == /\ maxBal  = [a \in Acceptor |-> -1]
        /\ maxAccBal = [a \in Acceptor |-> -1]
        /\ maxAccVal  = [a \in Acceptor |-> InitVal]
        /\ maxComBal = [a \in Acceptor |-> -1]
        /\ maxComVal  = [a \in Acceptor |-> InitVal]
        /\ msgs = {}
        /\ balValue = [b \in Ballot |->[expVal |-> InitVal, setVal |-> InitVal]]
        /\ history = <<>>
        /\ dataResult = [a \in Acceptor |-> [value |-> InitVal, version  |-> 1]]
        
Send(m) == msgs' = msgs \cup {m}
 
CAS(ev,sv,b) ==  /\ ~ \E m \in msgs: m.type = "Prepare" /\ m.bal = b 
                 /\ Send([type |-> "Prepare", bal |-> b])
                 /\ balValue' = [balValue EXCEPT ![b]=
                                 [expVal |-> ev, setVal |-> sv]]
                 /\ history' = Append(history,[type |-> "invoke", bal |-> b,
                             expVal |-> ev, setVal |-> sv, flag |-> "TURE"])
                 /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, 
                           maxComVal,dataResult>>        

\* Promise Message add ReadResult(value,version)                           
Promise(a) == 
  /\ \E m \in msgs : 
        /\ m.type = "Prepare"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "Promise", acc |-> a, bal |-> m.bal, 
                  maxAccBal |-> maxAccBal[a], maxAccVal |-> maxAccVal[a],
                  maxComBal |-> maxComBal[a], maxComVal |-> maxComVal[a],
                  value |->dataResult[a].value, 
                  version |->dataResult[a].version])
  /\ UNCHANGED <<maxAccBal, maxAccVal, maxComBal, maxComVal, 
                 balValue, history,dataResult>>

  
Propose(b) == /\ ~ \E m \in msgs: m.type = "Propose" /\ m.bal = b
              /\ \E Q \in Quorum :
                  LET Qmset == {m \in msgs : /\ m.type = "Promise"
                                             /\ m.acc \in Q
                                             /\ m.bal = b}
                      maxAccbal == Maximum({m.maxAccBal : m \in Qmset})
                      maxCombal == Maximum({m.maxComBal : m \in Qmset})
                      preValue == (CHOOSE m \in Qmset : m.maxAccBal=maxAccbal).maxAccVal
                      QResult == {m.value : m \in Qmset}
                      maxVersion == Maximum({m.version : m \in Qmset})
                      maxValue == (CHOOSE m \in Qmset : m.version=maxVersion).value
                  IN  /\ \A a \in Q : \E m \in Qmset : m.acc = a 
                      /\ IF maxAccbal > maxCombal  
                            THEN  /\ Send([type |-> "Propose", bal |-> b, val |-> preValue])
                                  /\ balValue'=[balValue EXCEPT ![b]= [expVal |-> balValue[maxAccbal].expVal, 
                                      setVal |-> preValue]]
                            ELSE  /\IF balValue[b].expVal = maxValue
                                      THEN   Send([type |-> "Propose", bal |-> b,
                                                 val |-> balValue[b].setVal])
                                      ELSE   Send([type |-> "Terminate", bal |-> b])
                                  /\ balValue' = balValue
                      \*/\ IF ~Same(QResult) THEN Send([type |-> "Repair",
                      \*                               value |-> maxValue,
                      \*                               version |-> maxVersion])
                      /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, 
                                     history,dataResult>>

                             
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
             /\ UNCHANGED<<maxComBal, maxComVal, dataResult, balValue, history>>   
             
Learn(b) == /\ ~\E m \in msgs : m.type = "Learn" /\ m.bal = b
            /\ \E Q \in Quorum :
                LET QAmset == {m \in msgs : /\ m.type="Accept"
                                            /\ m.acc \in Q
                                            /\ m.bal=b}
                IN /\ \A a \in Q : \E m \in QAmset : m.acc = a
            /\ Send([type |-> "Learn", bal |-> b, val |-> balValue[b].setVal])
            /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, 
                           maxComVal, balValue, history,dataResult>>
               
Ack(a) == /\ \E m \in msgs: /\ m.type="Learn"
                            /\ maxBal[a] \leq m.bal
                            /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                            /\ maxComBal' = [maxComBal EXCEPT ![a] = m.bal]
                            /\ maxComVal' = [maxComVal EXCEPT ![a] = m.val]
                            /\ dataResult' = [dataResult EXCEPT ![a]=
                                [value |-> m.val, version |->(@.version+1)]]
                            /\ Send([type |-> "Ack", bal |-> m.bal, 
                                    val |-> m.val, acc |->a])
          /\ UNCHANGED <<maxAccBal, maxAccVal, balValue, history>>
          
SelectMessages(type, b) == {m \in msgs : m.type = type /\ m.bal = b}
      
Acked(b) == /\ {m.acc : m \in SelectMessages("Ack",b) } \in Quorum
            /\ {hpos \in DOMAIN history : /\ history[hpos].type ="response" 
                                          /\ history[hpos].bal = b } = {}
            /\ history' = Append(history, [type |-> "response", bal |-> b,
                                          expVal |-> balValue[b].expVal,
                                          setVal |-> balValue[b].setVal,
                                          flag |->"TRUE"])
            /\ UNCHANGED <<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal,
                           balValue, msgs,dataResult>>
                    
Next == \/ \E ev, sv \in Value, b \in Ballot : CAS(ev,sv,b)
        \/ \E b \in Ballot : \/ Propose(b)
                             \/ Learn(b)
                             \/ Acked(b)
        \/ \E a \in Acceptor : \/ Promise(a)
                               \/ Accept(a)
                               \/ Ack(a)
                               \* \/ Repair(a)                         
              
Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
FiniteSeq(S) == UNION {[1..n -> S] : n \in 1..Cardinality(S)}
SeqAsSet(S) == {S[i] : i \in DOMAIN S}
IsResponse(r) == r.type = "response"
resHistory == SelectSeq(history, IsResponse)
RECURSIVE Check(_,_)
Check(seq,r) == IF seq = <<>> THEN TRUE
                ELSE LET cur == Head(seq)
                     IN \/ /\ cur.flag = "TRUE"
                           /\ cur.expVal = r
                           /\ Check(Tail(seq),cur.setVal)
                        \/ /\ cur.flag = "FALSE"
                           /\ cur.expVal # r
                           /\ Check(Tail(seq),r)
                           
HistoryIsLinearizable == \E order \in {<<>>} \union FiniteSeq(Ballot) :
    /\ \A H \in SeqAsSet(history) : H.type = "response" => H.bal \in SeqAsSet(order)
    /\ \A H1_i, H2_i \in DOMAIN history :
        (history[H1_i].type = "response" /\ history[H2_i].type = "invoke" /\ H1_i < H2_i) =>
            (
                history[H2_i].bal \in SeqAsSet(order) =>
                    \E i1, i2 \in DOMAIN order :
                        /\ order[i1] = history[H1_i].bal
                        /\ order[i2] = history[H2_i].bal
                        /\ i1 < i2
            )
    /\ \A i1, i2 \in DOMAIN order :
        i2 = i1 + 1 => balValue[order[i1]].setVal = balValue[order[i2]].expVal
    /\ order /= <<>> => InitVal = balValue[order[1]].expVal
    

Inv == /\ TypeOK
       /\ HistoryIsLinearizable
       
=============================================================================
\* Modification History
\* Last modified Fri Mar 11 12:51:16 CST 2022 by LENOVO
\* Created Sun Feb 27 08:57:09 CST 2022 by LENOVO
