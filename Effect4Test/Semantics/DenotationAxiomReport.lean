/-
Axiom receipts for the flow denotation (`test/contracts/flow-denotation.contract.md`).
Expected union: `propext` and `Quot.sound`.
-/

import Effect4.Semantics.Denotation

#print axioms Effects.reachableNoChoose_trans
#print axioms Effects.RawFlow.reachSet_length_lt_of_edge
#print axioms Effect4.Flow.edgeNoChoose_of_plan_jump
#print axioms Effect4.Flow.edgeNoChoose_of_plan_perform
#print axioms Effect4.Flow.tape_length_of_plan_choose
#print axioms Effect4.Flow.denoteGo_eq
#print axioms Effect4.Flow.interpretRun_pure
#print axioms Effect4.Flow.interpretRun_vis
#print axioms Effect4.Flow.interpretRun_run_perform
#print axioms Effect4.Flow.interpretRun_run_choose
#print axioms Effect4.Flow.traceHandler_writesLog
#print axioms Effect4.Flow.interpret_log_append
#print axioms Effect4.Flow.interpret_log_of_nil
#print axioms Effect4.Flow.loop_eq_interpretRun
#print axioms Effect4.Flow.runTape_eq_interpretRun
#print axioms Effect4.Flow.segmentBudget
#print axioms Effect4.Flow.decisionBudget
#print axioms Effect4.Flow.denoteFuel_eq_denoteGo
#print axioms Effect4.Flow.denoteFuel_eq_denote
#print axioms Effect4.Flow.runTape_eq_interpretRun_denote
#print axioms Effect4.Flow.runDefault_eq_interpretRun_denote
#print axioms Effect4.Flow.runDefault_no_fuel_frontier
