/-
Axiom receipts for the Flow runner (`test/contracts/flow-runner.contract.md`).
Expected union: `propext` and `Quot.sound`.
-/

import Effect4.Semantics.Runs

#print axioms Effect4.Flow.Tape.read_answered_length
#print axioms Effect4.Flow.step_choose_consumes_one
#print axioms Effect4.Flow.readArgs_of_bounded
#print axioms Effect4.Flow.plan_checked
#print axioms Effect4.Flow.step_checked
#print axioms Effect4.Flow.loop_checked_not_stuck
#print axioms Effect4.Flow.run_checked_not_stuck
#print axioms Effect4.Flow.loop_fuel_mono
#print axioms Effect4.Flow.run_fuel_mono
