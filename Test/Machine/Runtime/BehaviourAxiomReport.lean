import Test.Machine.Runtime.BehaviourContract

/-! Dependency receipts for BEH/obs, BEH/tape and their counterexamples. The
repository-wide gate checks generated equality and all auxiliary declarations. -/

#print axioms Effect4.Machine.Obs
#print axioms Effect4.Machine.instDecidableEqObs
#print axioms Effect4.Machine.Obs.le
#print axioms Effect4.Machine.Obs.le_refl
#print axioms Effect4.Machine.Obs.le_trans
#print axioms Effect4.Machine.obs
#print axioms Effect4.Machine.obs_mono_of_le_terminal
#print axioms Effect4.Machine.Beh
#print axioms Effect4.Machine.Beh_add
#print axioms Effect4.Machine.Beh_fuel_irrelevant
#print axioms Test.Runtime.BehaviourContract.frontiers_related
#print axioms Test.Runtime.BehaviourContract.observations_not_related
#print axioms Test.Runtime.BehaviourContract.frontier_projection_false
#print axioms Test.Runtime.BehaviourContract.empty_tape_suffices
