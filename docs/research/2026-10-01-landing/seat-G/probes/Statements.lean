import Effect4.Laws.Program.Guard.Decision
import Effect4.Laws.Program.Guard.Single

/-!
Seat G probe (2026-10-01, steps 1-2): the statement of every theorem steps 1 and 2 re-prove, and of
the decision-lift structure and its consumers, printed fully explicit (`pp.all`, universes on). Run
at the base (`logs/statements-before.log`) and after the change (`logs/statements-after.log`); the
two logs are diffed (`logs/statements.diff`). The `#print`s are the brief's before-and-after record
of the six Guard statements; their proof halves are expected to differ.
-/

open Lean Meta Elab Command

/-- The constant's type, fully explicit. -/
elab "#signature " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload id
  let ci ← getConstInfo name
  let fmt ← liftTermElabM <| withOptions
    (fun o => (o.setBool `pp.all true).setBool `pp.universes true) (ppExpr ci.type)
  logInfo m!"{name} :{indentD fmt}"

-- the lifting engine (step 1)
#signature Effect4.Machine.Lift.DecisionLift
#signature Effect4.Machine.Lift.DecisionLift.mk
#signature Effect4.Machine.Lift.loop_lift
#signature Effect4.Machine.Lift.loop_entry
#signature Effect4.Machine.Lift.fireFold_lift
#signature Effect4.Machine.Lift.fireState_lift
#signature Effect4.Machine.Lift.flushAllState_lift
#signature Effect4.Machine.Lift.advanceState_lift
#signature Effect4.Machine.Lift.stepDecisionState_lift
#signature Effect4.Machine.Lift.machineFact_stepDecision
-- the Guard statements (step 2)
#signature Effect4.Program.Guard.SingleGuard.held_fireStep
#signature Effect4.Program.Guard.SingleGuard.held_fireFold
#signature Effect4.Program.Guard.SingleGuard.held_fireState
#signature Effect4.Program.Guard.SingleGuard.held_flushAllState
#signature Effect4.Program.Guard.SingleGuard.held_advanceState
#signature Effect4.Program.Guard.SingleGuard.held_steppedBy
#signature Effect4.Program.Guard.OuterDriver.fireStep_preserved
#signature Effect4.Program.Guard.OuterDriver.fireFold_preserved
#signature Effect4.Program.Guard.OuterDriver.fireState_preserved
#signature Effect4.Program.Guard.OuterDriver.flushAllState_preserved
#signature Effect4.Program.Guard.OuterDriver.advanceState_preserved

#print Effect4.Program.Guard.SingleGuard.held_fireFold
#print Effect4.Program.Guard.SingleGuard.held_flushAllState
#print Effect4.Program.Guard.SingleGuard.held_advanceState
#print Effect4.Program.Guard.OuterDriver.fireFold_preserved
#print Effect4.Program.Guard.OuterDriver.flushAllState_preserved
#print Effect4.Program.Guard.OuterDriver.advanceState_preserved

#print axioms Effect4.Machine.Lift.loop_lift
#print axioms Effect4.Machine.Lift.loop_entry
#print axioms Effect4.Machine.Lift.fireFold_lift
#print axioms Effect4.Machine.Lift.fireState_lift
#print axioms Effect4.Machine.Lift.flushAllState_lift
#print axioms Effect4.Machine.Lift.advanceState_lift
#print axioms Effect4.Machine.Lift.stepDecisionState_lift
#print axioms Effect4.Program.Guard.SingleGuard.held_fireFold
#print axioms Effect4.Program.Guard.SingleGuard.held_fireState
#print axioms Effect4.Program.Guard.SingleGuard.held_flushAllState
#print axioms Effect4.Program.Guard.SingleGuard.held_advanceState
#print axioms Effect4.Program.Guard.OuterDriver.fireFold_preserved
#print axioms Effect4.Program.Guard.OuterDriver.fireState_preserved
#print axioms Effect4.Program.Guard.OuterDriver.flushAllState_preserved
#print axioms Effect4.Program.Guard.OuterDriver.advanceState_preserved
