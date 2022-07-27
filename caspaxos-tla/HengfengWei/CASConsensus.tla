---------------------------- MODULE CASConsensus ----------------------------
(*
CASConsensus is an operational semantics (or a reference model) of linearizable CAS registers.

TODO: how to model "linearizable CAS registers"?
how to distinguish it from "sequentially consistent CAS registers"?

Refs (TODO: Google for other references on operational semantics):

- "Model Checking Linearizability via Refinement"
  at https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/linearizability.pdf
- "MonkeyDB: Effectively Testing Correctness under Weak Isolation Levels"
  at https://www.microsoft.com/en-us/research/uploads/prod/2021/09/main.pdf
- "Using Lightweight Formal Methods to Validate a Key-Value Storage Node in Amazon S3"
  at https://assets.amazon.science/07/6c/81bfc2c243249a8b8b65cc2135e4/using-lightweight-formal-methods-to-validate-a-key-value-storage-node-in-amazon-s3.pdf
*)

=============================================================================
\* Modification History
\* Last modified Wed Jul 27 10:08:20 CST 2022 by hengxin
\* Created Wed Jul 27 00:22:59 CST 2022 by hengxin