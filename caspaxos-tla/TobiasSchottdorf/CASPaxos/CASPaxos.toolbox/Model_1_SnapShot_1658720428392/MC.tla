---- MODULE MC ----
EXTENDS CASPaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Acceptors
const_165872042537148000 == 
{a1, a2, a3}
----

\* CONSTANT definitions @modelParameterConstants:0Values
const_165872042537149000 == 
{0, 1, 2, 3}
----

\* CONSTANT definitions @modelParameterConstants:2Mutator(b, v)
const_165872042537150000(b, v) == 
(1 + b*v) % 4
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_165872042537151000 ==
0..3
----
\* INIT definition @modelBehaviorInit:0
init_165872042537152000 ==
/\  accepted = (a1 :> 2 @@ a2 :> 2 @@ a3 :> 0)
/\  msgs = { [type |-> "prepare-req", bal |-> 1],
  [type |-> "prepare-req", bal |-> 2],
  [accepted |-> 1, type |-> "accept-rsp", acc |-> a1],
  [accepted |-> 2, type |-> "accept-rsp", acc |-> a1],
  [accepted |-> 2, type |-> "accept-rsp", acc |-> a2],
  [type |-> "accept-req", bal |-> 1, newVal |-> 1],
  [type |-> "accept-req", bal |-> 2, newVal |-> 3],
  [ accepted |-> 0,
    type |-> "prepare-rsp",
    acc |-> a1,
    promised |-> 1,
    val |-> 0 ],
  [ accepted |-> 0,
    type |-> "prepare-rsp",
    acc |-> a2,
    promised |-> 2,
    val |-> 0 ],
  [ accepted |-> 0,
    type |-> "prepare-rsp",
    acc |-> a3,
    promised |-> 1,
    val |-> 0 ],
  [ accepted |-> 1,
    type |-> "prepare-rsp",
    acc |-> a1,
    promised |-> 2,
    val |-> 1 ] }
/\  prepared = (a1 :> 2 @@ a2 :> 2 @@ a3 :> 1)
/\  value = (a1 :> 3 @@ a2 :> 3 @@ a3 :> 0)
----
=============================================================================
\* Modification History
\* Created Mon Jul 25 11:40:25 CST 2022 by hengxin
