---- MODULE MC ----
EXTENDS CASPaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Acceptors
const_165872044624259000 == 
{a1, a2, a3}
----

\* CONSTANT definitions @modelParameterConstants:0Values
const_165872044624260000 == 
{0, 1, 2, 3}
----

\* CONSTANT definitions @modelParameterConstants:2Mutator(b, v)
const_165872044624261000(b, v) == 
(1 + b*v) % 4
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_165872044624262000 ==
0..3
----
=============================================================================
\* Modification History
\* Created Mon Jul 25 11:40:46 CST 2022 by hengxin
