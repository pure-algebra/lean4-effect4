import Effect4.Laws.Program.Agreement.Machine

/-!
Fresh kernel dependency report for the agreement of the compile with the denotation
(`src/Effect4/Laws/Program/Agreement.lean`, `src/Effect4/Laws/Program/Agreement/Machine.lean`; packet
`Test/contracts/program-denotation.contract.md`).

Coordinator-owned, appended from the `#print axioms` output at each landing. Every theorem
below is expected at the ceiling `propext`/`Quot.sound`; the gate
(`Test/Audit/AxiomGate.lean`) is what enforces it, this file is the human-readable receipt.
-/

-- The fragment and its measures.
#print axioms Effect4.Program.Agreement.Plain
#print axioms Effect4.Program.Agreement.depth
#print axioms Effect4.Program.Agreement.steps
#print axioms Effect4.Program.Agreement.depth_pos

-- The local machine.
#print axioms Effect4.Program.Agreement.localStep
#print axioms Effect4.Program.Agreement.localRun
#print axioms Effect4.Program.Agreement.localRun_mono
#print axioms Effect4.Program.Agreement.localRun_congr
#print axioms Effect4.Program.Agreement.popFrom_pass
#print axioms Effect4.Program.Agreement.step_failure_pass_onSuccess
#print axioms Effect4.Program.Agreement.step_success_pass_onFailure

-- The compile, one arm at a time, and the hooks at an address.
#print axioms Effect4.Program.Agreement.compileEff_bind
#print axioms Effect4.Program.Agreement.compileEff_perform_sync
#print axioms Effect4.Program.Agreement.suspendBodyAt_of_at
#print axioms Effect4.Program.Agreement.suspendBodyAt_suspend
-- P1a (2026-09-06): the host's exit fold and the fuel-zero clause it needs.
#print axioms Effect4.Program.Agreement.compileEff_exit
#print axioms Effect4.Program.Agreement.compileEff_exit_fold
#print axioms Effect4.Program.Agreement.compileEff_exit_frame
#print axioms Effect4.Program.Agreement.compileEff_at_zero
#print axioms Effect4.Program.Agreement.meaning_of_asExit
#print axioms Effect4.Program.Agreement.Plain.not_gen
#print axioms Effect4.Program.Agreement.Plain.not_whileLoop
#print axioms Effect4.Program.Agreement.suspendBodyAt_branch_bad
#print axioms Effect4.Program.Agreement.resolve_of_at

-- The agreement over the frame machine.
#print axioms Effect4.Program.Agreement.Reaches.trans
#print axioms Effect4.Program.Agreement.localRun_compile
#print axioms Effect4.Program.Agreement.localRun_root

-- The invariants of the simulation.
#print axioms Effect4.Program.Agreement.plainCode_compileEff
#print axioms Effect4.Program.Agreement.plain_at
#print axioms Effect4.Program.Agreement.plainCode_suspendBodyAt
#print axioms Effect4.Program.Agreement.localStep_plain
#print axioms Effect4.Program.Agreement.syncOpStep_quiet
#print axioms Effect4.Program.Agreement.localStep_quiet
#print axioms Effect4.Program.Agreement.dueResumes_quiet
#print axioms Effect4.Program.Agreement.step_fst_success
#print axioms Effect4.Program.Agreement.step_fst_failure
#print axioms Effect4.Program.Agreement.evaluatePrim_localStep

-- The finalizer mask (`E4-DEN-CE-004`, repaired).
#print axioms Effect4.Program.Agreement.Plain_eq_Straight
#print axioms Effect4.Program.Agreement.exitFrom_ext
#print axioms Effect4.Program.Agreement.step_ofExit_onExit
#print axioms Effect4.Program.Agreement.step_ofExit_finalizer
#print axioms Effect4.Program.Agreement.popFrom_pass_setInterruptible
#print axioms Effect4.Program.Agreement.step_ofExit_pass_setInterruptible

-- The commands, one local step each.
#print axioms Effect4.Program.Agreement.iteration_M
#print axioms Effect4.Program.Agreement.drive_loop_sync_op
#print axioms Effect4.Program.Agreement.drive_loop_running
#print axioms Effect4.Program.Agreement.drive_loop_finish
#print axioms Effect4.Program.Agreement.drive_deliver_running
#print axioms Effect4.Program.Agreement.drive_deliver_finish
#print axioms Effect4.Program.Agreement.drive_drainDue
#print axioms Effect4.Program.Agreement.drive_finish_M
#print axioms Effect4.Program.Agreement.drive_evaluate_load

-- The yield past the budget (`E4-DEN-CE-005`, repaired): the park, the fire, the rounds.
#print axioms Effect4.Program.Agreement.parkedAt
#print axioms Effect4.Program.Agreement.Myield
#print axioms Effect4.Program.Agreement.drive_loop_yield
#print axioms Effect4.Program.Agreement.fire_Myield
#print axioms Effect4.Program.Agreement.fire_Myield_answer
#print axioms Effect4.Program.Agreement.Owes
#print axioms Effect4.Program.Agreement.Owes.step
#print axioms Effect4.Program.Agreement.Owes.finish
#print axioms Effect4.Program.Agreement.Owes.yield
#print axioms Effect4.Program.Agreement.flushAll_Myield

-- The simulation and the packet's theorem.
#print axioms Effect4.Program.Agreement.drive_localRun
#print axioms Effect4.Program.Agreement.replay_Mexit
#print axioms Effect4.Program.Agreement.run_eq_meaning
