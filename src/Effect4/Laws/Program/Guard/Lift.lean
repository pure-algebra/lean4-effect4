import Effect4.Laws.Program.Guard.Decision
import Effect4.Laws.Program.Guard.OuterDriver

/-!
Concept: reactive-scheduling R9 and store-typing R4.
Question: the application answer-flow proofs need the driver's actual command authority.
Reach: native decisions, pending commands, and detached scheduler snapshots.
The existing guard proof supplies its state, reserved keys, and queue facts unchanged.
Consumer: the coupled driver invariant for Workers, QueueWorkers, and Timeout.
This connector supplies no application answer class or progress statement.
-/
set_option autoImplicit false
namespace Effect4.Program.Guard
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Guard.RegistrationQueue

/-- The pending queue retains the proved guard facts and registration tail. -/
abbrev DriverQueue (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (commands : List NCmd) : Prop := GuardQueue root table m commands ∧ RegistrationQueue commands

/-- Detached tasks retain their reserved keys and the source-independent race exclusion. -/
abbrev DriverTasks (m : NativeMachine) (tasks : List NTask) : Prop :=
  ReservedKeys m (tasks.flatMap taskKeys) ∧ ∀ task ∈ tasks, taskRaceSites task = []

/-- The existing request-preservation producer projects to its actual guard invariant. -/
theorem state_fold_lift (root : NativeEff) (table : RowTable) :
    letI := evaluatorFor root table
    Lift.FoldLift Lift.unitOrder (interpOf root table) (fun _ m => GuardState m)
      (fun _ m commands => DriverQueue root table m commands)
      (fun _ m tasks => DriverTasks m tasks) := by
  letI := evaluatorFor root table
  have base := fun m => OuterDriver.preserved_foldLift root table (driverContract root table) m
  constructor
  · intro tasks world m command rest running held
    obtain ⟨next, moved, after⟩ := (base m).step tasks () m command rest running
      ⟨OuterDriver.Preserved.refl held.1, held.2⟩
    exact ⟨next, moved, after.1.state, after.2⟩
  · intro world m
    exact (base m).nil () m
  · intro world m owner fiber held found
    have after := (base m).drain () m owner fiber (OuterDriver.Preserved.refl held) found
    exact ⟨after.1.state, after.2⟩
  · intro world m owner task held
    exact ((base m).ran () m owner task (OuterDriver.Preserved.refl held)).state
  · intro world m owner task tasks held running pending
    exact (base m).task () m owner task tasks (OuterDriver.Preserved.refl held) running pending
  · intro world m task tasks pending
    exact (base m).skip () m task tasks pending
  · intro world m millis state held running clock
    obtain ⟨next, moved, after⟩ := (base m).clockNone () m millis state
      (OuterDriver.Preserved.refl held) running clock
    exact ⟨next, moved, after.state⟩
  · intro world m millis owed state held running clock
    obtain ⟨next, moved, after, pending⟩ := (base m).clockSome () m millis owed state
      (OuterDriver.Preserved.refl held) running clock
    exact ⟨next, moved, after.state, pending⟩

/-- Every decision carries guard state with the actual pending and detached authority.
The prepared external reply runs before the internal queue's reserved-key condition applies. -/
theorem state_decision_lift (root : NativeEff) (table : RowTable) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table) (fun _ m => GuardState m)
      (fun _ m commands => DriverQueue root table m commands)
      (fun _ m tasks => DriverTasks m tasks) (fun _ _ _ => True) := by
  letI := evaluatorFor root table
  have folded := state_fold_lift root table
  refine {
    step := folded.step, nil := folded.nil, drain := folded.drain, ran := folded.ran,
    task := folded.task, skip := folded.skip, clockNone := folded.clockNone, clockSome := folded.clockSome,
    evaluate := ?_, yield := ?_, interrupt := ?_, middleware := ?_, answer := ?_ }
  · intro world m id held running
    exact ⟨LocalDecision.guardQueue_evaluate_drainDue root table m id, trivial, trivial, trivial⟩
  · intro world m id verdict held
    exact LocalDecision.guardState_yieldVerdict root table 0 m id verdict held
  · intro world m who extra target fiber held found
    have self : m.fiber? fiber.id = some fiber := by rw [fiber_id_of_lookup found]; exact found
    exact LocalDecision.guardState_interruptBeforeLoop root table m target fiber who extra held self
  · intro world m held
    exact LocalDecision.guardState_installMiddleware root table 0 m held
  · intro world m id token answer held running admitted
    have prepared := AnswerDecision.guardState_prepareAsyncAnswer root table m id token answer held
    have shape := AnswerDecision.prepareAsyncAnswer_shape root table m id token answer
    refine ⟨(), trivial, ?_, fun _ => ⟨?_, ?_⟩⟩
    · exact guardState_driveStep_resume root table _ id token _ [.drainDue] prepared shape.2.2
    · exact ⟨AnswerDecision.guardQueue_resume_from_tail root table _ id token _ [.drainDue]
        prepared (AnswerDecision.guardQueue_drainDue root table _),
        AnswerDecision.registrationQueue_resume_result root table _ id token _ [.drainDue]
          ⟨trivial, trivial⟩⟩
    · exact ⟨reservedKeys_nil _, fun _ member => False.elim (List.not_mem_nil member)⟩

end Effect4.Program.Guard
