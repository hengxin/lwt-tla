------------------------- MODULE GryadkaCasRegister -------------------------
(*
Written by Greg Rogers

TLA+ code: https://gist.github.com/grogers0/c7e87f9dfe58c6070b19db9d3c073b72

Post (A TLA+ specification for Gryadka): https://medium.com/@grogepodge/tla-specification-for-gryadka-c80cd625944e
*)

EXTENDS Integers, Sequences, FiniteSets
-----------------------------------------------------------------------------
\* Timestamps is the set of possible timestamps for operations to choose from.
\*     Each operation uses a unique timestamp.
\* Values is the set of possible values to set the register to.
\* Acceptors is the set of nodes which act as acceptors in the paxos sense.
\* Quorums is the set of all possible quorums, typically simple majorities.
CONSTANTS Timestamps, Values, Acceptors, Quorums

ASSUME Timestamps \subseteq Nat
ASSUME IsFiniteSet(Timestamps)
NoTS == -1
ASSUME NoTS \notin Timestamps

ASSUME Quorums \subseteq SUBSET Acceptors
ASSUME \A q1, q2 \in Quorums : q1 \intersect q2 /= {}

\* The initial value is chosen arbitrarily
InitVal == CHOOSE v \in Values : TRUE

\* msgs is the buffer of all messages. Messages can be delivered out of order or duplicated.
\* ops is the mapping from timestamp to CAS(old, new) for operations being proposed.
\* acceptorTS is the timestamp each acceptor is prepared for, only operations which match this value are accepted.
\* acceptorValTS is the timestamp of the last accepted value for each acceptor, or NoTS is none has been accepted yet.
\* acceptorValue is the last accepted value for each acceptor, or InitVal if none has been accepted yet.
\* history is the actual order of invoke/response actions for the operations identified by the timestamp.
VARIABLES msgs, ops, acceptorTS, acceptorValTS, acceptorValue, history
-----------------------------------------------------------------------------
Messages == [type: {"prepare"}, acceptor: Acceptors, ts: Timestamps]
     \union [type: {"promise"}, acceptor: Acceptors, ts: Timestamps,
             prevTS: Timestamps \union {NoTS}, prevVal: Values]
     \union [type: {"accept"}, acceptor: Acceptors, ts: Timestamps, val: Values]
     \union [type: {"accepted"}, acceptor: Acceptors, ts: Timestamps, val: Values]
\* Each operation represents a CAS from an oldVal to a newVal. In Gryadka,
\*     reads are treated the same as CAS(val, val)
Operations == [oldVal: Values, newVal: Values]
Events == [type: {"invoke", "response"}, ts: Timestamps]

TypeOK == /\ msgs \subseteq Messages
          /\ ops \in [Timestamps -> Operations]
          /\ acceptorTS \in [Acceptors -> Timestamps \union {NoTS}]
          /\ acceptorValTS \in [Acceptors -> Timestamps \union {NoTS}]
          /\ acceptorValue \in [Acceptors -> Values]
          /\ history \in Seq(Events)

Init == /\ msgs = {}
        /\ ops \in [Timestamps -> Operations]
        /\ acceptorTS = [a \in Acceptors |-> NoTS]
        /\ acceptorValTS = [a \in Acceptors |-> NoTS]
        /\ acceptorValue = [a \in Acceptors |-> InitVal]
        /\ history = <<>>

-----------------------------------------------------------------------------
SelectMessages(type, ts) == {m \in msgs : m.type = type /\ m.ts = ts}
PromisedValue(ts) == LET promiseMsgs == SelectMessages("promise", ts)
                     IN (CHOOSE m \in promiseMsgs : \A m2 \in promiseMsgs : m.prevTS >= m2.prevTS).prevVal
-----------------------------------------------------------------------------
Prepare(ts) == /\ SelectMessages("prepare", ts) = {} \* Each timestamp must be unique
               /\ msgs' = msgs \union [type: {"prepare"}, acceptor: Acceptors, ts: {ts}]
               /\ history' = Append(history, [type |-> "invoke", ts |-> ts])
               /\ UNCHANGED <<ops, acceptorTS, acceptorValTS, acceptorValue>>

RecvPrepare(a, ts) == /\ acceptorTS[a] = NoTS \/ acceptorTS[a] < ts
                      /\ acceptorTS' = [acceptorTS EXCEPT ![a] = ts]
                      /\ msgs' = msgs \union {[type |-> "promise", acceptor |-> a, ts |-> ts,
                                               prevTS |-> acceptorValTS[a], prevVal |-> acceptorValue[a]]}
                      /\ UNCHANGED <<ops, acceptorValTS, acceptorValue, history>>

Accept(ts) == /\ {m.acceptor : m \in SelectMessages("promise", ts)} \in Quorums
              /\ ops[ts].oldVal = PromisedValue(ts)
              /\ msgs' = msgs \union [type: {"accept"}, acceptor: Acceptors, ts: {ts}, val: {ops[ts].newVal}]
              /\ UNCHANGED <<ops, acceptorTS, acceptorValTS, acceptorValue, history>>

RecvAccept(a, ts, v) == /\ acceptorTS[a] = ts
                        /\ acceptorValTS' = [acceptorValTS EXCEPT ![a] = ts]
                        /\ acceptorValue' = [acceptorValue EXCEPT ![a] = v]
                        /\ msgs' = msgs \union [type: {"accepted"}, acceptor: {a}, ts: {ts}, val: {v}]
                        /\ UNCHANGED <<ops, acceptorTS, history>>

Accepted(ts) == /\ {m.acceptor : m \in SelectMessages("accepted", ts)} \in Quorums
                /\ {hpos \in DOMAIN history : history[hpos] = [type |-> "response", ts |-> ts]} = {}
                /\ history' = Append(history, [type |-> "response", ts |-> ts])
                /\ UNCHANGED <<msgs, ops, acceptorTS, acceptorValTS, acceptorValue>>

Next == \/ \E ts \in Timestamps : \/ Prepare(ts)
                                  \/ Accept(ts)
                                  \/ Accepted(ts)
        \/ \E m \in msgs : \/ m.type = "prepare" /\ RecvPrepare(m.acceptor, m.ts)
                           \/ m.type = "accept" /\ RecvAccept(m.acceptor, m.ts, m.val)

Spec == Init /\ [][Next]_<<msgs, ops, acceptorTS, acceptorValTS, acceptorValue, history>>
-----------------------------------------------------------------------------
FiniteSeq(S) == UNION {[1..n -> S] : n \in 1..Cardinality(S)}
SeqAsSet(S) == {S[i] : i \in DOMAIN S}

HistoryIsLinearizable == \E order \in {<<>>} \union FiniteSeq(Timestamps) :
    /\ \A H \in SeqAsSet(history) : H.type = "response" => H.ts \in SeqAsSet(order)
    /\ \A H1_i, H2_i \in DOMAIN history :
        (history[H1_i].type = "response" /\ history[H2_i].type = "invoke" /\ H1_i < H2_i) =>
            (
                history[H2_i].ts \in SeqAsSet(order) =>
                    \E i1, i2 \in DOMAIN order :
                        /\ order[i1] = history[H1_i].ts
                        /\ order[i2] = history[H2_i].ts
                        /\ i1 < i2
            )
    /\ \A i1, i2 \in DOMAIN order :
        i2 = i1 + 1 => ops[order[i1]].newVal = ops[order[i2]].oldVal
    /\ order /= <<>> => InitVal = ops[order[1]].oldVal

Inv == /\ TypeOK
       /\ HistoryIsLinearizable

=============================================================================