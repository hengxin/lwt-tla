
(************************************************************************************                                                     
Repair(a) == /\ \E m \in msgs: /\ m.type="Repair"
                               /\ dataResult' = [dataResult EXCEPT ![a] =
                                                   [value |-> m.value, 
                                                   version |-> m.version]]
             /\ UNCHANGED<<maxBal, maxAccBal, maxAccVal, maxComBal, maxComVal, 
                           msgs, balValue>>
************************************************************************************)

