/-
Axiom receipts for the `plan` inversions (`Effect4/Semantics/PlanInversion.lean`).

Expected union for every declaration below: `propext` and `Quot.sound` -- the
trace lane's ceiling. `Classical.choice` is forbidden here and does not appear:
every inversion is a structural case analysis on the block's terminator and the
tape read, and the two `testValue` readings are decisions about a `Val`.

These receipts were part of
`Effect4Test/Target/TypeScript/SkeletonSemanticsAxiomReport.lean` until
2026-09-03, when the lemmas moved out of the TypeScript target namespace
(survey finding L7). `plan_performCatch_inv`, `testValue_some` and
`testValue_ne` had no receipt there and gain one here.
-/

import Effect4.Semantics.PlanInversion

#print axioms Effect4.Flow.testValue_some
#print axioms Effect4.Flow.testValue_ne
#print axioms Effect4.Flow.plan_ret_inv
#print axioms Effect4.Flow.plan_jump_inv
#print axioms Effect4.Flow.plan_perform_inv
#print axioms Effect4.Flow.plan_performCatch_inv
#print axioms Effect4.Flow.plan_choose_inv
#print axioms Effect4.Flow.plan_exhausted_inv
#print axioms Effect4.Flow.plan_mismatch_inv
