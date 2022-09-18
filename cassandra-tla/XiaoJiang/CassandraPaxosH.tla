-------------------------- MODULE CassandraPaxosH --------------------------
(*
CassandraPaxos spec with the "history" variable.
*)

EXTENDS CassandraPaxos, Sequences, FiniteSets, TLC
----------------------------------------------------------------------------
Event == [type : {"invocation", "response"}, bal : Ballot]
----------------------------------------------------------------------------
VARIABLES history

varsH == <<vars, history>>
----------------------------------------------------------------------------
TypeOKH ==
  /\ TypeOK
  /\ history \in Seq(Event)
----------------------------------------------------------------------------
InitH ==
  /\ Init
  /\ history = <<>>
----------------------------------------------------------------------------
Phase1aH(b) ==
  /\ Phase1a(b)
  \* Every CAS operation has an "invocation" event.
  /\ history' = Append(history, [type |-> "invocation", bal |-> b])

Phase1bH(a) ==
  /\ Phase1b(a)
  /\ UNCHANGED <<history>>

Phase2aH(b) ==
  /\ Phase2a(b)
  /\ UNCHANGED <<history>>

Phase2bH(a) ==
  /\ Phase2b(a)
  /\ UNCHANGED <<history>>

Phase3aH(b, v) ==
  /\ Phase3a(b, v)
  /\ UNCHANGED <<history>>

Phase3bH(a) ==
  /\ Phase3b(a)
  /\ UNCHANGED <<history>>

RespondH(b) ==
  /\ Respond(b)
  \* Not all CAS operations have a "response" event. Some do not terminate.
  /\ history' = Append(history, [type |-> "response", bal |-> b])
----------------------------------------------------------------------------
NextH ==
  \/ \E b \in Ballot :
       \/ Phase1aH(b)
       \/ Phase2aH(b)
       \/ \E v \in Value : Phase3aH(b, v)
       \/ RespondH(b)
  \/ \E a \in Acceptor :
       \/ Phase1bH(a)
       \/ Phase2bH(a)
       \/ Phase3bH(a)

SpecH == InitH /\ [][NextH]_varsH /\ WF_varsH(NextH)
----------------------------------------------------------------------------
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
    
Inv == HistoryIsLinearizable(CompleteHistory(history))
Prop == <>[](HistoryIsLinearizable(CompleteHistory(history)))

=============================================================================
\* Modification History
\* Last modified Sun Sep 18 16:48:55 CST 2022 by 875
\* Created Sun Sep 18 16:42:01 CST 2022 by 875
