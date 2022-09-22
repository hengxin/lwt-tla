----------------------------- MODULE CASPaxosH -----------------------------
(*
CASPaxos spec with the "history" variable.
*)

EXTENDS CASPaxos, Sequences
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

Phase2aH(b, v) ==
  /\ Phase2a(b, v)
  /\ UNCHANGED <<history>>

Phase2bH(a) ==
  /\ Phase2b(a)
  /\ UNCHANGED <<history>>

RespondH(b) ==
  /\ Respond(b)
  \* Not all CAS operations have a "response" event. Some do not terminate.
  /\ history' = Append(history, [type |-> "response", bal |-> b])
----------------------------------------------------------------------------
NextH ==
  \/ \E b \in Ballot :
       \/ Phase1aH(b)
       \/ \E v \in Value : Phase2aH(b, v)
       \/ RespondH(b)
  \/ \E a \in Acceptor :
       \/ Phase1bH(a)
       \/ Phase2bH(a)

SpecH == InitH /\ [][NextH]_varsH
=============================================================================
\* Modification History
\* Last modified Wed Jul 27 09:23:18 CST 2022 by hengxin
\* Created Tue Jul 26 23:30:04 CST 2022 by hengxin