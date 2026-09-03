/-
Axiom receipts for the region denotation (`test/contracts/flow-denotation.contract.md`,
the D2 third). Expected union: `propext` and `Quot.sound`. No `Classical.choice`:
`String` stays out of the module and every proof is a `StateT` computation.
-/

import Effect4.Semantics.RegionDenotation

#print axioms Effect4.Flow.regionHandler_run_enter
#print axioms Effect4.Flow.regionHandler_run_perform
#print axioms Effect4.Flow.regionHandler_run_decide
#print axioms Effect4.Flow.regionHandler_run_acquire_nil
#print axioms Effect4.Flow.regionHandler_run_acquire_cons
#print axioms Effect4.Flow.regionHandler_run_leave_nil
#print axioms Effect4.Flow.regionHandler_run_leave_cons
#print axioms Effect4.Flow.regionHandler_run_fail
#print axioms Effect4.Flow.regionTracedService_run
#print axioms Effect4.Flow.interpretRegionsFrom_run_pure
#print axioms Effect4.Flow.interpretRegionsFrom_run_vis
#print axioms Effect4.Flow.interpretRegionsFrom_run_handled_pure
#print axioms Effect4.Flow.interpretRegionsFrom_run_handled_bind
#print axioms Effect4.Flow.interpretRegionsFrom_run_perform
#print axioms Effect4.Flow.interpretRegionsFrom_run_decide
#print axioms Effect4.Flow.interpretRegionsFrom_run_enter
#print axioms Effect4.Flow.interpretRegionsFrom_run_acquire_nil
#print axioms Effect4.Flow.interpretRegionsFrom_run_acquire_cons
#print axioms Effect4.Flow.interpretRegionsFrom_run_leave_nil
#print axioms Effect4.Flow.interpretRegionsFrom_run_leave_cons
#print axioms Effect4.Flow.interpretRegionsFrom_run_fail
#print axioms Effect4.Flow.fail_eq_interpret
#print axioms Effect4.Flow.stuck_eq_interpret
#print axioms Effect4.Flow.regionLoop_eq_interpret
#print axioms Effect4.Flow.runRegionsCause_eq_interpret
#print axioms Effect4.Flow.runRegions_eq_interpret
#print axioms Effect4.Flow.runRegionsDefault_eq_interpret
#print axioms Effect4.Flow.lookupBlock_erase
#print axioms Effect4.Flow.block?_id
#print axioms Effect4.Flow.allPlain_of_all
#print axioms Effect4.Flow.toRegionService_handle
#print axioms Effect4.Flow.toRegionService_pure
#print axioms Effect4.Flow.regionLoop_erase
#print axioms Effect4.Flow.runRegions_erase
