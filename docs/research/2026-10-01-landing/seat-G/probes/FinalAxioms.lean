import Effect4.Laws
import Test.Program.GuardFoldLift
import Test.Schema.DialectContract
import Test.Audit.ExhaustiveFixture

/-! Seat G probe (step 6): `#print axioms` of every declaration seat G added or re-proved, after
the final build. -/

-- step 1: the lifting engine
#print axioms Effect4.Machine.Lift.FoldLift
#print axioms Effect4.Machine.Lift.FoldLift.ofDecisionLift
#print axioms Effect4.Machine.Lift.driveState_one
#print axioms Effect4.Machine.Lift.FoldLift.loop_lift
#print axioms Effect4.Machine.Lift.FoldLift.loop_entry
#print axioms Effect4.Machine.Lift.FoldLift.fireFold_lift
#print axioms Effect4.Machine.Lift.FoldLift.fireState_lift
#print axioms Effect4.Machine.Lift.FoldLift.flushAllState_lift
#print axioms Effect4.Machine.Lift.FoldLift.advanceState_lift
#print axioms Effect4.Machine.Lift.loop_lift
#print axioms Effect4.Machine.Lift.loop_entry
#print axioms Effect4.Machine.Lift.fireFold_lift
#print axioms Effect4.Machine.Lift.fireState_lift
#print axioms Effect4.Machine.Lift.flushAllState_lift
#print axioms Effect4.Machine.Lift.advanceState_lift
#print axioms Effect4.Machine.Lift.stepDecisionState_lift
#print axioms Effect4.Machine.Lift.machineFact_stepDecision
-- step 2: the Guard instances and the re-proved statements
#print axioms Effect4.Program.Guard.SingleGuard.held_foldLift
#print axioms Effect4.Program.Guard.SingleGuard.held_fireFold
#print axioms Effect4.Program.Guard.SingleGuard.held_fireState
#print axioms Effect4.Program.Guard.SingleGuard.held_flushAllState
#print axioms Effect4.Program.Guard.SingleGuard.held_advanceState
#print axioms Effect4.Program.Guard.OuterDriver.clockStep_owed_guardQueue
#print axioms Effect4.Program.Guard.OuterDriver.preserved_foldLift
#print axioms Effect4.Program.Guard.OuterDriver.advanceTick_preserved
#print axioms Effect4.Program.Guard.OuterDriver.fireFold_preserved
#print axioms Effect4.Program.Guard.OuterDriver.fireState_preserved
#print axioms Effect4.Program.Guard.OuterDriver.flushAllState_preserved
#print axioms Effect4.Program.Guard.OuterDriver.advanceState_preserved
#print axioms Test.Program.GuardFoldLift.held_parked
#print axioms Test.Program.GuardFoldLift.edit_unparks
#print axioms Test.Program.GuardFoldLift.interrupt_field_false
#print axioms Test.Program.GuardFoldLift.no_decisionLift
#print axioms Test.Program.GuardFoldLift.held_is_foldLift
-- step 3: the inventory (meta code; the gate binds its module at the implementation ceiling)
#print axioms Effect4.Laws.Auto.Exhaustive.elabExhaustiveGate
-- step 5: the requirement key and its battery
#print axioms Effect4.Schema.Bridge.requirementKey
#print axioms Effect4.Schema.Bridge.effDocument
#print axioms Test.Schema.DialectContract.requirementKey_eq_keyText
#print axioms Test.Schema.DialectContract.requirementKey_injective
#print axioms Test.Schema.DialectContract.nameOnlyKey
#print axioms Test.Schema.DialectContract.twoServices
