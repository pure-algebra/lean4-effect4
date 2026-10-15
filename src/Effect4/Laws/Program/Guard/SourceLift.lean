import Effect4.Laws.Program.Guard.Lift
import Effect4.Laws.Program.NativeReplies
import Effect4.Laws.Machine.LiftCoupledFact

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the crews' answer-flow proofs need source facts with actual command authority.
Reach: direct lexical programs and every native decision, including prepared external replies.
Consumer: Workers.Assertions.logs_step and QueueWorkers.Assertions.logs_history.
The connector combines existing invariants; it supplies no acquired-value class or store predicate.
-/
set_option autoImplicit false
namespace Effect4.Program.Guard
open Effect4 Effect4.Machine Effect4.Program

/-- Existing source ownership advances independently alongside the actual driver's guard. -/
theorem source_coupled (root : NativeEff) (fragment : SourceScope.Fragment root) (table : RowTable) :
    letI := evaluatorFor root table
    Lift.CoupledDecision (p := Lift.unitOrder) (interp := interpOf root table)
      (J := fun (_ : Unit) m => GuardState m)
      (I := fun _ m commands => DriverQueue root table m commands)
      (O := fun _ m tasks => DriverTasks m tasks) (A := fun _ _ _ => True)
      (P := fun _ m => SourceScope.ConfigurationAt root m)
      (Q := fun _ _ commands => SourceScope.CommandsAt root commands)
      (R := fun _ _ tasks => SourceScope.TasksAt root tasks) := by
  letI := evaluatorFor root table
  exact (SourceScope.reply_decision_lift root fragment table).asCoupled
    (by intros; trivial)

/-- The command driver retains source ownership and its guard in one decision invariant. -/
theorem source_decision_lift (root : NativeEff) (fragment : SourceScope.Fragment root) (table : RowTable) :
    letI := evaluatorFor root table
    Lift.DecisionLift (Lift.pairOrder Lift.unitOrder Lift.unitOrder) (interpOf root table)
      (fun _ m => GuardState m ∧ SourceScope.ConfigurationAt root m)
      (fun _ m commands => DriverQueue root table m commands ∧ SourceScope.CommandsAt root commands)
      (fun _ m tasks => DriverTasks m tasks ∧ SourceScope.TasksAt root tasks)
      (fun _ _ _ => True) := by
  letI := evaluatorFor root table
  exact (state_decision_lift root table).withCoupledFact (source_coupled root fragment table)

end Effect4.Program.Guard
