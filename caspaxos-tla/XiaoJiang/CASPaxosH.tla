----------------------------- MODULE CASPaxosH -----------------------------
(*
CASPaxos spec with the "history" variable.
*)

EXTENDS CASPaxos, Sequences, FiniteSets, TLC
----------------------------------------------------------------------------
Event == [type : {"invocation", "response"}, bal : Ballot]
----------------------------------------------------------------------------
VARIABLES history,
    done

varsH == <<vars, history, done>>
----------------------------------------------------------------------------
TypeOKH ==
  /\ TypeOK
  /\ done \in [Ballot -> {0, 1}]
  /\ history \in Seq(Event)
----------------------------------------------------------------------------
InitH ==
  /\ Init
  /\ Cardinality({ops[i].swapVal : i \in Ballot}) = Cardinality(Ballot)
  /\ history = <<>>
  /\ done = [b \in Ballot |-> 0]
----------------------------------------------------------------------------
Phase1aH(b) ==
  /\ Phase1a(b)
  \* Every CAS operation has an "invocation" event.
  /\ history' = Append(history, [type |-> "invocation", bal |-> b])
  /\ UNCHANGED <<done>>

Phase1bH(a) ==
  /\ Phase1b(a)
  /\ UNCHANGED <<history, done>>

Phase2aH(b, v) ==
  /\ Phase2a(b, v)
  /\ UNCHANGED <<history, done>>

Phase2bH(a) ==
  /\ Phase2b(a)
  /\ UNCHANGED <<history, done>>

RespondH(b) ==
  /\ Respond(b)
  \* Not all CAS operations have a "response" event. Some do not terminate.
  /\ history' = Append(history, [type |-> "response", bal |-> b])
  /\ done' = [done EXCEPT ![b] = 1]

\* for first n - 1 ballots
NoEnough2BFail(b) ==
  /\ done[b] = 0
  /\ Cardinality({a\in Acceptor: /\ maxBal[a] > b
                                 /\ ~\E m \in msgs: (/\ m.type = "2b"
                                                     /\ m.bal = b
                                                     /\ m.acc = a)}) > (Cardinality(Acceptor) \div 2)
  /\ done' = [done EXCEPT ![b] = 1]
  /\ UNCHANGED <<vars, history>>

\* for final ballot
FinalNotMatchFail(b, v) ==
  /\ b = mBallot
  /\ done[b] = 0
  /\ \A a \in Acceptor: \E m \in msgs: /\ m.type = "1b" 
                                       /\ m.bal = b
  /\ ~(\E Q \in Quorum :
        LET Q1b == {m \in msgs : /\ m.type = "1b"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
            Q1bv == {m \in Q1b : m.mbal >= 0}
        IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a 
            /\ \/ /\ Q1bv = {}  \* <<+>> CAS(None, v) as an initialization operation
                  /\ ops[b].cmpVal = None  \* <<+>>
               \/ /\ \A a \in Q : \E m \in Q1bv : m.acc = a \* a quorum has value v
                  /\ \E m \in Q1bv :  \* <<+>> CAS(v, ops[b].swapVal) as an atomic compare-and-swap operation
                     /\ m.mval = v
                     /\ \A mm \in Q1bv : m.mbal = mm.mbal \* value v comes from same ballot
                     /\ ops[b].cmpVal = v)  \* <<+>> not all CAS operations will terminate due to this precondition
  /\ done' = [done EXCEPT ![b] = 1]
  /\ UNCHANGED <<vars, history>>
----------------------------------------------------------------------------
NextH ==
  \/ \E b \in Ballot :
       \/ Phase1aH(b)
       \/ \E v \in Value : Phase2aH(b, v)
       \/ RespondH(b)
       \/ NoEnough2BFail(b)
       \/ \E v \in Value : FinalNotMatchFail(b, v)
  \/ \E a \in Acceptor :
       \/ Phase1bH(a)
       \/ Phase2bH(a)

SpecH == InitH /\ [][NextH]_varsH /\ WF_varsH(NextH)
----------------------------------------------------------------------------
AllDone == \A b \in Ballot: done[b] = 1

FiniteSeq(S) == UNION {[1..n -> S] : n \in 1..Cardinality(S)}
SeqAsSet(S) == {S[i] : i \in DOMAIN S}
HistoryBallot(H) == {H[i].bal : i \in DOMAIN H}
HasResponse(h, HSeq) == HSeq # <<>> /\ \E H \in SeqAsSet(HSeq): H.type = "response" /\ H.bal = h.bal
RECURSIVE CompleteHistory(_)
CompleteHistory(H) == IF H = <<>> THEN <<>>
                                  ELSE LET cur == Head(H)
                                       IN  IF cur.type = "response" THEN <<cur>> \o CompleteHistory(Tail(H))
                                                                    ELSE IF HasResponse(cur, Tail(H)) THEN <<cur>> \o CompleteHistory(Tail(H))
                                                                                                     ELSE CompleteHistory(Tail(H))
RECURSIVE CHistorySet2CHistory(_, _)
CHistorySet2CHistory(CHistorySet, value) ==
  IF CHistorySet = {} THEN <<>>
                      ELSE IF \A x \in CHistorySet : ~(x.type = "invocation" /\ ops[x.bal].cmpVal = value)
                              THEN <<>>
                              ELSE LET c == CHOOSE x \in CHistorySet : x.type = "invocation" /\ ops[x.bal].cmpVal = value
                                   IN <<c.bal>> \o CHistorySet2CHistory(CHistorySet \ {c}, ops[c.bal].swapVal)
                           
\* HistoryIsLinearizable(CHistory) ==   
\*     LET order == CHistorySet2CHistory(SeqAsSet(CHistory), None)
\*     IN 
\*     /\ HistoryBallot(CHistory) \subseteq Ballot
\*     /\ \A H \in SeqAsSet(CHistory) : H.type = "response" => H.bal \in SeqAsSet(order)
\*     /\ \A H \in SeqAsSet(CHistory) : H.type = "invocation" => (\E H2 \in SeqAsSet(CHistory): H2.bal = H.bal /\ H2.type = "response")
\*     /\ \A H1_i, H2_i \in DOMAIN CHistory :
\*         (CHistory[H1_i].type = "response" /\ CHistory[H2_i].type = "invocation" /\ H1_i < H2_i /\ CHistory[H1_i].bal # CHistory[H2_i].bal) =>
\*             (
\*                 CHistory[H2_i].bal \in SeqAsSet(order) =>
\*                     \E i1, i2 \in DOMAIN order :
\*                         /\ order[i1] = CHistory[H1_i].bal
\*                         /\ order[i2] = CHistory[H2_i].bal
\*                         /\ i1 < i2
\*             )
\*     /\ \A i1, i2 \in DOMAIN order :
\*         i2 = i1 + 1 => ops[order[i1]].swapVal = ops[order[i2]].cmpVal
\*     /\ order /= <<>> => None = ops[order[1]].cmpVal


HistoryIsLinearizable(CHistory) == 
\/ CHistory = <<>>
\/ \E order \in {<<>>} \union FiniteSeq(HistoryBallot(CHistory)) :
   /\ HistoryBallot(CHistory) \subseteq Ballot
   /\ \A H \in SeqAsSet(CHistory) : H.type = "response" => H.bal \in SeqAsSet(order)
   /\ \A H \in SeqAsSet(CHistory) : H.type = "invocation" => (\E H2 \in SeqAsSet(CHistory): H2.bal = H.bal /\ H2.type = "response")
   /\ \A H1_i, H2_i \in DOMAIN CHistory :
       (CHistory[H1_i].type = "response" /\ CHistory[H2_i].type = "invocation" /\ H1_i < H2_i /\ CHistory[H1_i].bal # CHistory[H2_i].bal) =>
           (
               CHistory[H2_i].bal \in SeqAsSet(order) =>
                   \E i1, i2 \in DOMAIN order :
                       /\ order[i1] = CHistory[H1_i].bal
                       /\ order[i2] = CHistory[H2_i].bal
                       /\ i1 < i2
           )
   /\ \A i1, i2 \in DOMAIN order :
       i2 = i1 + 1 => ops[order[i1]].swapVal = ops[order[i2]].cmpVal
   /\ order /= <<>> => None = ops[order[1]].cmpVal
       
Inv == ~AllDone\/HistoryIsLinearizable(CompleteHistory(history))

=============================================================================
\* Modification History
\* Last modified Mon Nov 14 23:26:40 CST 2022 by 875
\* Last modified Wed Jul 27 09:23:18 CST 2022 by hengxin
\* Created Tue Jul 26 23:30:04 CST 2022 by hengxin