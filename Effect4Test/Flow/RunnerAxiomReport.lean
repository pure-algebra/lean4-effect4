/-
Axiom receipts for the Flow runner (`test/contracts/flow-runner.contract.md`).
Expected union: `propext` and `Quot.sound`.
-/

import Effect4.Semantics.Runs
import Effect4.Semantics.Fuel

#print axioms Effect4.Flow.Tape.read_answered_length
#print axioms Effect4.Flow.Tape.read_mismatch_ne
#print axioms Effect4.Flow.RunResult.refusal_self
#print axioms Effect4.Flow.RunResult.refusal_of_read
#print axioms Effect4.Flow.RunResult.exhausted_refusal
#print axioms Effect4.Flow.RunResult.stuck_refusal
#print axioms Effect4.Flow.RunResult.refusal_ne_failed
#print axioms Effect4.Flow.RunResult.refusal_ne_done
#print axioms Effect4.Flow.idBind
#print axioms Effect4.Flow.idMap
#print axioms Effect4.Flow.idPure
#print axioms Effect4.Flow.step_choose_consumes_one
#print axioms Effect4.Flow.readArgs_of_bounded
#print axioms Effect4.Flow.plan_checked
#print axioms Effect4.Flow.step_checked
#print axioms Effect4.Flow.loop_checked_not_stuck
#print axioms Effect4.Flow.run_checked_not_stuck
#print axioms Effect4.Flow.loop_fuel_mono
#print axioms Effect4.Flow.run_fuel_mono

-- The fuel argument (`Effect4/Semantics/Fuel.lean`).
#print axioms Effects.lookupBlock_id
#print axioms Effects.mem_blockIds_of_lookup
#print axioms Effect4.Flow.plan_shape
#print axioms Effect4.Flow.step_progress
#print axioms Effect4.Flow.LoopBudget.segment_lt
#print axioms Effect4.Flow.loop_budget_not_exhausted
#print axioms Effect4.Flow.loop_fuelFor_not_exhausted
#print axioms Effect4.Flow.run_fuelFor_finishes
#print axioms Effect4.Flow.runDefault_finishes
#print axioms Effect4.Flow.run_fuel_ge_finishes
#print axioms Effect4.Flow.step_not_failed
#print axioms Effect4.Flow.loop_not_failed
#print axioms Effect4.Flow.run_not_failed
#print axioms Effect4.Flow.run_fuelFor_answered
