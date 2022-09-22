---- MODULE MC ----
EXTENDS CASPaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Acceptors
const_165872016546422000 == 
{a1, a2, a3}
----

\* CONSTANT definitions @modelParameterConstants:0Values
const_165872016546423000 == 
{0, 1, 2, 3}
----

\* CONSTANT definitions @modelParameterConstants:2Mutator(b, v)
const_165872016546424000(b, v) == 
(1 + b*v) % 4
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_165872016546425000 ==
0..3
----
=============================================================================
\* Modification History
\* Created Mon Jul 25 11:36:05 CST 2022 by hengxin
