import Effect4.Laws.Program.PlaceFunding.FlowGuarded

/-!
# Overwatch probe: the guarded producers generalize the merged ones exactly

Concept: store-typing R4 and scope-lifetime-finalization R11. Claim: the proposed
`answer-flow-history` and `place-ledger-history` (seat FLOW's receipt). Consumer: the four
answer-flow goals, through `FlowGuarded`.

Question. Codex's `LocalOn.guarded_decision_lift` (`PlaceFunding/FlowGuarded.lean`) restates the
merged `LocalOn.decision_lift` (`PlaceFunding/Flow.lean`) over any driver invariant. Is the merged
theorem its instance, so that the merged proof can go?

Reach. Every place ledger, carried invariant, program, row table and cap.
Not established. Nothing beyond the two statements; no application instance.
-/

set_option autoImplicit false

namespace Overwatch.LiftLayer
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Program.PlaceFunding
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

/-- The merged decision lift is the guarded one at the reply driver's queue and snapshot facts. -/
theorem decision_lift_is_instance {L : Ledger} {Free : NCode → Prop} {root : NativeEff}
    {table : RowTable} {Q : NativeMachine → Prop} (facts : LocalOn L Free root table Q) (cap : Nat)
    (carried : letI := evaluatorFor root table
      Lift.DecisionLift Lift.unitOrder (interpOf root table)
        (fun _ m => ConfigurationAt root m ∧ Q m)
        (fun _ _ cmds => CommandsAt root cmds) (fun _ _ tasks => TasksAt root tasks)
        (fun _ _ _ => True)) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ m => (ConfigurationAt root m ∧ Q m) ∧ Holds L cap m)
      (fun _ _ cmds => CommandsAt root cmds) (fun _ _ tasks => TasksAt root tasks)
      (fun _ _ _ => True) :=
  facts.guarded_decision_lift cap Lift.unitOrder _ _ _ (fun _ _ _ queued => queued) carried

/-- Reader: both proofs state one proposition. -/
theorem same_statement {L : Ledger} {Free : NCode → Prop} {root : NativeEff}
    {table : RowTable} {Q : NativeMachine → Prop} (facts : LocalOn L Free root table Q) (cap : Nat)
    (carried : letI := evaluatorFor root table
      Lift.DecisionLift Lift.unitOrder (interpOf root table)
        (fun _ m => ConfigurationAt root m ∧ Q m)
        (fun _ _ cmds => CommandsAt root cmds) (fun _ _ tasks => TasksAt root tasks)
        (fun _ _ _ => True)) :
    facts.decision_lift cap carried = decision_lift_is_instance facts cap carried := rfl

end Overwatch.LiftLayer
