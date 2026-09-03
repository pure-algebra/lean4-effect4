import Effect4Test.Semantics.RegionSimulationContract

/-!
# Region-simulation kernel dependency report

Packet D4, the finalizer half. Every authored public theorem of
`Effect4/Semantics/RegionSimulation.lean` is listed exactly once, in module
order, together with the three instances of `regions_simulate` the contract
names. The accepted ceiling is no dependency, `propext`, or `propext` with
`Quot.sound`; `Classical.choice` and project-local axioms are not admitted.

The fence A and fence B theorems this packet consumes —
`Effect4.FrameFiber.run_add`, `.run_add_running`, `.run_mono`,
`.run_succ_finished`, `.run_succ_running`, `.popFrom_continue_*`,
`.resumeValue_*`, `.resumeCause_*` — are receipted in
`Effect4Test/Runtime/FramesAxiomReport.lean` and are not repeated here.
-/

/-! ## R1 — the projection between the merged failure list and a cause -/

#print axioms Effect4.RegionSimulation.failuresOfCause_causeOfFailures
#print axioms Effect4.RegionSimulation.find_fail_causeOfFailures
#print axioms Effect4.RegionSimulation.combine_reasons_cons
#print axioms Effect4.RegionSimulation.toOutcome_combine

/-! ## R2 — the two `onExit` transitions -/

#print axioms Effect4.RegionSimulation.step_onExit_failure
#print axioms Effect4.RegionSimulation.step_onExit_success

/-! ## R3 — the finalizer half of the machine -/

#print axioms Effect4.RegionSimulation.unwind_failure
#print axioms Effect4.RegionSimulation.close_success

/-! ## R4 — the instances of `regions_simulate` -/

#print axioms Effect4Test.Semantics.RegionSimulationContract.regions_simulate_regionBothSucceed
#print axioms Effect4Test.Semantics.RegionSimulationContract.regions_simulate_regionNested
#print axioms Effect4Test.Semantics.RegionSimulationContract.regions_simulate_regionTwoFail
#print axioms Effect4Test.Semantics.RegionSimulationContract.runnerSide_regionBothSucceed
#print axioms Effect4Test.Semantics.RegionSimulationContract.runnerSide_regionNested
#print axioms Effect4Test.Semantics.RegionSimulationContract.runnerSide_regionTwoFail
