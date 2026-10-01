import Effect4.Laws.Program.Guard.Decision
import Effect4.Laws.Program.Guard.Single
import Test.Program.GuardFoldLift

/-! Seat G probe (step 2): the axioms of the two fold-lift instances, the six fold-level theorems
re-proved through them, the two `fire` theorems re-proved beside them, the decision-level users,
and the battery's theorems. -/

#print axioms Effect4.Program.Guard.SingleGuard.held_foldLift
#print axioms Effect4.Program.Guard.OuterDriver.preserved_foldLift
#print axioms Effect4.Program.Guard.SingleGuard.held_fireFold
#print axioms Effect4.Program.Guard.SingleGuard.held_flushAllState
#print axioms Effect4.Program.Guard.SingleGuard.held_advanceState
#print axioms Effect4.Program.Guard.OuterDriver.fireFold_preserved
#print axioms Effect4.Program.Guard.OuterDriver.flushAllState_preserved
#print axioms Effect4.Program.Guard.OuterDriver.advanceState_preserved
#print axioms Effect4.Program.Guard.SingleGuard.held_fireState
#print axioms Effect4.Program.Guard.OuterDriver.fireState_preserved
#print axioms Effect4.Program.Guard.SingleGuard.held_steppedBy
#print axioms Effect4.Program.Guard.SingleGuard.held_executePrefix
#print axioms Effect4.Program.Guard.guardState_steppedBy
#print axioms Effect4.Program.Guard.requestOrInterrupted_steppedBy
#print axioms Effect4.Program.Guard.guardState_executePrefix
#print axioms Test.Program.GuardFoldLift.held_parked
#print axioms Test.Program.GuardFoldLift.edit_unparks
#print axioms Test.Program.GuardFoldLift.interrupt_field_false
#print axioms Test.Program.GuardFoldLift.no_decisionLift
#print axioms Test.Program.GuardFoldLift.held_is_foldLift
