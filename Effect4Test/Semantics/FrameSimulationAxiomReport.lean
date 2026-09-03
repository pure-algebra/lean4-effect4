import Effect4.Semantics.FrameSimulation

/-!
# Frame-simulation kernel dependency report

Every authored public theorem named by `test/contracts/frame-simulation.contract.md`
is listed exactly once, in contract order. The accepted ceiling is no dependency,
`propext`, or `propext` with `Quot.sound`; `Classical.choice` and project-local
axioms are not admitted.

The fence A theorems this packet consumes — `Effect4.FrameFiber.run_add`,
`.run_add_finished`, `.run_add_running`, `.run_mono`,
`.step_preserves_uninterrupted` and the two skip/defer consequences — are
receipted in `Effect4Test/Runtime/FramesAxiomReport.lean` section F10 and are not
repeated here.
-/

/-! ## F1 — the exit bijection -/

#print axioms Effect4.FrameSimulation.exceptOf_exitOf
#print axioms Effect4.FrameSimulation.exitOf_exceptOf

/-! ## F4 — the fragment is closed -/

#print axioms Effect4.FrameSimulation.compile_inFragment
#print axioms Effect4.FrameSimulation.tapeContA_inFragment

/-! ## F5 — the two machine transitions -/

#print axioms Effect4.FrameSimulation.step_push
#print axioms Effect4.FrameSimulation.step_answer

/-! ## F6 — the algebra side and the residual bookkeeping -/

#print axioms Effect4.FrameSimulation.interpret_pure
#print axioms Effect4.FrameSimulation.interpret_vis
#print axioms Effect4.FrameSimulation.residual_append

/-! ## F7 — the workhorse -/

#print axioms Effect4.FrameSimulation.run_in_context

/-! ## F8 — the theorem and its `Cause.fail` corollary -/

#print axioms Effect4.FrameSimulation.compile_simulates
#print axioms Effect4.FrameSimulation.run_liftFail
#print axioms Effect4.FrameSimulation.compile_simulates_fail
