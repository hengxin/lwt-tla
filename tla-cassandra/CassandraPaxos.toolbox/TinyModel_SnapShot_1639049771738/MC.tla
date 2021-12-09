---- MODULE MC ----
EXTENDS CassandraPaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Acceptor
const_1639049750229259000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions Value
const_1639049750229260000 == 
{v1, v2}
----

\* CONSTANT definitions @modelParameterConstants:2Quorum
const_1639049750229261000 == 
{{a1,a2},{a1,a3},{a2,a3}}
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1639049750229263000 ==
0..1
----
=============================================================================
\* Modification History
\* Created Thu Dec 09 19:35:50 CST 2021 by LENOVO
