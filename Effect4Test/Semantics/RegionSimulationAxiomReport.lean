import Effect4Test.Semantics.RegionSimulationContract

/-!
# Region-simulation kernel dependency report

Packet D4, the finalizer half, as repaired by spike S4 (compile repairs P1, P2
and P3, and the T5/T6 statements with their instances). Every authored public
theorem of `Effect4/Semantics/RegionSimulation.lean` is listed exactly once, in
module order, together with the instances of `regions_simulate` the contract
names. The accepted ceiling is no dependency, `propext`, or `propext` with
`Quot.sound`; `Classical.choice` and project-local axioms are not admitted.

The fence A and fence B theorems this packet consumes —
`Effect4.FrameFiber.run_add`, `.run_add_running`, `.run_mono`,
`.run_succ_finished`, `.run_succ_running`, `.popFrom_continue_*`,
`.resumeValue_*`, `.resumeCause_*` — are receipted in
`Effect4Test/Runtime/FramesAxiomReport.lean` and are not repeated here.
-/

/-! ## R1 — P1: one scope per region, and its close result -/

#print axioms Effect4.RegionSimulation.closeFinish_nil
#print axioms Effect4.RegionSimulation.closeFinish_single
#print axioms Effect4.RegionSimulation.closeFinish_many
#print axioms Effect4.RegionSimulation.closeFinish_eq_result?
#print axioms Effect4.RegionSimulation.closeExit_reasons
#print axioms Effect4.RegionSimulation.closeExit_success_iff
#print axioms Effect4.RegionSimulation.regionInterp_finalizerExit

/-! ## R2 — P2: a live frontier stays live -/

#print axioms Effect4.RegionSimulation.compileRegion_not_failure
#print axioms Effect4.RegionSimulation.compileRegion_never_fails
#print axioms Effect4.RegionSimulation.regionSuspendBody_frontier
#print axioms Effect4.RegionSimulation.regionSuspendBody_zero
#print axioms Effect4.RegionSimulation.step_suspend_fixed
#print axioms Effect4.RegionSimulation.run_suspend_fixed
#print axioms Effect4.RegionSimulation.regionInterp_suspend_fixed
#print axioms Effect4.RegionSimulation.compileAt_zero_fuel_live

/-! ## R3 — P3: `performCatch` as `onSuccessAndFailure` -/

#print axioms Effect4.RegionSimulation.regionSuspendBody_catch
#print axioms Effect4.RegionSimulation.compileRegion_catchFree
#print axioms Effect4.RegionSimulation.step_onSuccessAndFailure_answers
#print axioms Effect4.RegionSimulation.step_onSuccessAndFailure_answers_cause

/-! ## R4 — the projection between the merged failure list and a cause -/

#print axioms Effect4.RegionSimulation.failuresOfCause_causeOfFailures
#print axioms Effect4.RegionSimulation.find_fail_causeOfFailures
#print axioms Effect4.RegionSimulation.combine_reasons_cons
#print axioms Effect4.RegionSimulation.toOutcome_combine
#print axioms Effect4.RegionSimulation.toOutcome_append

/-! ## R5 — the machine transitions a close uses -/

#print axioms Effect4.RegionSimulation.step_onExit_failure
#print axioms Effect4.RegionSimulation.step_onExit_success
#print axioms Effect4.RegionSimulation.step_onSuccess_answers

/-! ## R6 — the finalizer half of the machine, with the per-name premise -/

#print axioms Effect4.RegionSimulation.unwind_failure
#print axioms Effect4.RegionSimulation.close_success_of
#print axioms Effect4.RegionSimulation.close_success
#print axioms Effect4.RegionSimulation.close_success_region
#print axioms Effect4.RegionSimulation.unwind_to_frame

/-! ## R7 — the same three on a compiled run, with no premise at all -/

#print axioms Effect4.RegionSimulation.unwind_failure_region
#print axioms Effect4.RegionSimulation.close_success_region_compiled
#print axioms Effect4.RegionSimulation.unwind_to_frame_region

/-! ## R7b — P1 as a general law: one scope, one row per registration, one exit -/

#print axioms Effect4.RegionSimulation.closeNames_releaseFrames
#print axioms Effect4.RegionSimulation.closeable_releaseFrames
#print axioms Effect4.RegionSimulation.region_close_rows
#print axioms Effect4.RegionSimulation.region_unwind_rows

/-! ## R8 — P4: the oracle agreement and the instances of T5 and T6 -/

#print axioms Effect4.RegionSimulation.statelessOracle_agrees
#print axioms Effect4Test.Semantics.RegionSimulationContract.oracle_agrees
#print axioms Effect4Test.Semantics.RegionSimulationContract.T5_regionBothSucceed
#print axioms Effect4Test.Semantics.RegionSimulationContract.T5_regionNested
#print axioms Effect4Test.Semantics.RegionSimulationContract.T5_regionTwoFail
#print axioms Effect4Test.Semantics.RegionSimulationContract.T5_regionReleaseFails
#print axioms Effect4Test.Semantics.RegionSimulationContract.T5_regionCatch
#print axioms Effect4Test.Semantics.RegionSimulationContract.T6_regionBothSucceed
#print axioms Effect4Test.Semantics.RegionSimulationContract.T6_regionNested
#print axioms Effect4Test.Semantics.RegionSimulationContract.T6_regionTwoFail
#print axioms Effect4Test.Semantics.RegionSimulationContract.T6_regionReleaseFails
#print axioms Effect4Test.Semantics.RegionSimulationContract.T6_regionCatch

/-! ## R9 — the trace instances and their pinned literals -/

#print axioms Effect4Test.Semantics.RegionSimulationContract.regions_simulate_regionBothSucceed
#print axioms Effect4Test.Semantics.RegionSimulationContract.regions_simulate_regionNested
#print axioms Effect4Test.Semantics.RegionSimulationContract.regions_simulate_regionTwoFail
#print axioms Effect4Test.Semantics.RegionSimulationContract.regions_simulate_regionReleaseFails
#print axioms Effect4Test.Semantics.RegionSimulationContract.regions_simulate_regionCatch
#print axioms Effect4Test.Semantics.RegionSimulationContract.runnerSide_regionBothSucceed
#print axioms Effect4Test.Semantics.RegionSimulationContract.runnerSide_regionNested
#print axioms Effect4Test.Semantics.RegionSimulationContract.runnerSide_regionTwoFail
#print axioms Effect4Test.Semantics.RegionSimulationContract.runnerSide_regionReleaseFails
#print axioms Effect4Test.Semantics.RegionSimulationContract.runnerSide_regionCatch

/-! ## R10 — the registration and catch-shape receipts -/

#print axioms Effect4Test.Semantics.RegionSimulationContract.registrations_regionBothSucceed
#print axioms Effect4Test.Semantics.RegionSimulationContract.registrations_regionTwoFail
#print axioms Effect4Test.Semantics.RegionSimulationContract.registrations_regionReleaseFails
#print axioms Effect4Test.Semantics.RegionSimulationContract.registrations_regionNested
#print axioms Effect4Test.Semantics.RegionSimulationContract.regionCatch_emits_caught
#print axioms Effect4Test.Semantics.RegionSimulationContract.regionBothSucceed_catch_free
#print axioms Effect4Test.Semantics.RegionSimulationContract.regionNested_catch_free
#print axioms Effect4Test.Semantics.RegionSimulationContract.regionTwoFail_catch_free
#print axioms Effect4Test.Semantics.RegionSimulationContract.regionReleaseFails_catch_free

/-! ## R11 — spike S4b: the leave configuration, and the proof that the walk is
the runner

One lemma per runner arm, the close lemma, the induction, and the corollaries
that let `regionInterp.contA` resume a region where the runner resumes it. -/

#print axioms Effect4.RegionSimulation.logOperation_prefix
#print axioms Effect4.RegionSimulation.regionLoop_jump
#print axioms Effect4.RegionSimulation.regionLoop_choose
#print axioms Effect4.RegionSimulation.regionLoop_perform
#print axioms Effect4.RegionSimulation.regionLoop_performCatch_ok
#print axioms Effect4.RegionSimulation.regionLoop_performCatch_error
#print axioms Effect4.RegionSimulation.regionLoop_enter
#print axioms Effect4.RegionSimulation.regionLoop_acquire
#print axioms Effect4.RegionSimulation.regionLoop_leave
#print axioms Effect4.RegionSimulation.anyReleaseFails_cons
#print axioms Effect4.RegionSimulation.closeReleases_cons_ok
#print axioms Effect4.RegionSimulation.statelessAnswer_of
#print axioms Effect4.RegionSimulation.registeredReleases_nil
#print axioms Effect4.RegionSimulation.closeReleases_success
#print axioms Effect4.RegionSimulation.closeFrame_success
#print axioms Effect4.RegionSimulation.closeWalk_agrees_regionLoop
#print axioms Effect4.RegionSimulation.leaveConfig_agrees_runRegions
#print axioms Effect4.RegionSimulation.leaveConfig_of_regionWalk
#print axioms Effect4.RegionSimulation.regionRegistrations_of_regionWalk
#print axioms Effect4.RegionSimulation.regionInterp_regionCont_resume
#print axioms Effect4.RegionSimulation.RunPrefix.refl
#print axioms Effect4.RegionSimulation.RunPrefix.of_eq
#print axioms Effect4.RegionSimulation.RunPrefix.trans
#print axioms Effect4.RegionSimulation.RunPrefix.emit

/-! ## R12 — spike S4b: the leave-configuration receipts and the inverted
boundary witness -/

#print axioms Effect4Test.Semantics.RegionSimulationContract.leaveConfig_regionBothSucceed
#print axioms Effect4Test.Semantics.RegionSimulationContract.enterPoint_regionBothSucceed
#print axioms Effect4Test.Semantics.RegionSimulationContract.leaveConfig_regionReleaseFails
#print axioms Effect4Test.Semantics.RegionSimulationContract.leaveConfig_regionCatch
#print axioms Effect4Test.Semantics.RegionSimulationContract.leaveConfig_regionTwoFail
#print axioms Effect4Test.Semantics.RegionSimulationContract.leaveConfig_regionNested
