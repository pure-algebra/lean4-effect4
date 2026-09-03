/-
Axiom receipts for the DB-04 approximation laws (`docs/TRACE-DAG.md`, row
`approximation`), region half. Expected union: `propext` and `Quot.sound`.
No `Classical.choice`: the fuel argument reproves its pigeonhole step by
structural induction (`Effect4/Semantics/Fuel.lean`) rather than reaching for
`List.Nodup.length_le_of_subset`.
-/

import Effect4.Semantics.Approximation

-- the three properties the region laws travel on
#print axioms Effect4.Flow.logOperation_appends
#print axioms Effect4.Flow.closeReleases_appends
#print axioms Effect4.Flow.closeFrame_appends
#print axioms Effect4.Flow.unwind_appends
#print axioms Effect4.Flow.fail_appends
#print axioms Effect4.Flow.fail_sound
#print axioms Effect4.Flow.obsOf_extends
#print axioms Effect4.Flow.regionLoop_sound
#print axioms Effect4.Flow.regionLoop_below
#print axioms Effect4.Flow.regionLoop_settles

-- the region analogues of the runner-half laws
#print axioms Effect4.Flow.regionStep_log_extends
#print axioms Effect4.Flow.regionLoop_fuel_stable
#print axioms Effect4.Flow.regionLoop_frontier_live
#print axioms Effect4.Flow.regionLoop_failed_head
#print axioms Effect4.Flow.region_obs_mono
#print axioms Effect4.Flow.region_obs_chain
#print axioms Effect4.Flow.regionObservation_stable
#print axioms Effect4.Flow.runRegionsObservation_wire
#print axioms Effect4.Flow.runRegionsObservation_eq
#print axioms Effect4.Flow.runRegions_obs_mono
#print axioms Effect4.Flow.runRegions_obs_chain
#print axioms Effect4.Flow.runRegions_obs_stable
#print axioms Effect4.Flow.runRegionsColimit_settled
#print axioms Effect4.Flow.runRegionsColimit_eq_of_settled

-- the region fuel formula and its sufficiency
#print axioms Effect4.Flow.lookupBlock_erase
#print axioms Effect4.Flow.block?_of_lookup_erase
#print axioms Effect4.Flow.LoopBudget.advance
#print axioms Effect4.Flow.LoopBudget.consume
#print axioms Effect4.Flow.fail_not_exhausted
#print axioms Effect4.Flow.regionLoop_budget_not_exhausted
#print axioms Effect4.Flow.regionFuelFor_blocks
#print axioms Effect4.Flow.regionFlow_erase_wf
#print axioms Effect4.Flow.runRegionsCause_fuelFor_finishes
#print axioms Effect4.Flow.runRegions_fuelFor_finishes
#print axioms Effect4.Flow.runRegionsDefault_finishes
#print axioms Effect4.Flow.runRegionsColimitDefault_settled
#print axioms Effect4.Flow.runRegionsColimitDefault_above
#print axioms Effect4.Flow.runRegionsColimitDefault_stable
#print axioms Effect4.Flow.runRegionsColimit_eq_default
