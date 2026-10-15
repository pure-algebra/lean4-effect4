import Effect4.Laws.Program.AnswerSlots.InitializedQueue
import Effect4.Laws.Program.AnswerSlots.InitializedDriver

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the initialized command invariant holds through actual scheduler and decision entry.
Consumers: the common crew log history and its two concrete application goals.
Reach: certified lexical sources without races, every command budget and prepared external reply.
The local command connection remains explicit until the queue producer supplies it.
No progress or outside-host agreement follows.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

abbrev DriverState (spec : Spec) (_ : Unit × Unit) (machine : NativeMachine) : Prop :=
  (Guard.GuardState machine ∧ SourceScope.ConfigurationAt spec.root machine) ∧ ParkedShape.Configuration machine

abbrev DriverQueue (spec : Spec) (_ : Unit × Unit) (machine : NativeMachine)
    (commands : List Guard.NCmd) : Prop :=
  Guard.DriverQueue spec.root spec.table machine commands ∧ SourceScope.CommandsAt spec.root commands

abbrev DriverTasks (spec : Spec) (_ : Unit × Unit) (machine : NativeMachine)
    (tasks : List Guard.NTask) : Prop :=
  Guard.DriverTasks machine tasks ∧ SourceScope.TasksAt spec.root tasks

/-- Every due entry contributes only its existing resume command. -/
theorem due_demand (spec : Spec) (machine : NativeMachine) (due : List (Owed NCode)) :
    QueueAt spec (drainOwed machine due).1 ((drainOwed machine due).2 ++ [.drainDue]) := by
  intro command member
  rcases List.mem_append.mp member with pending | last
  · obtain ⟨owed, present, rfl⟩ := Guard.drainOwed_commands machine due command pending
    exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
  · rw [List.mem_singleton.mp last]
    exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩

/-- Prepared reply entry leaves only ordinary evaluation and due-drain commands. -/
theorem resume_demand (spec : Spec) (machine : NativeMachine) (id : FiberId) (token : Nat) (code : NCode) :
    letI := evaluatorFor spec.root spec.table
    QueueAt spec (driveStep (interpOf spec.root spec.table) machine (.resume id token code) [.drainDue]).1
      (driveStep (interpOf spec.root spec.table) machine (.resume id token code) [.drainDue]).2 := by
  letI := evaluatorFor spec.root spec.table
  have singleton (after : NativeMachine) : QueueAt spec after [.drainDue] := by
    intro command member
    rw [List.mem_singleton.mp member]
    exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
  have started (after : NativeMachine) : QueueAt spec after [.evaluate id, .drainDue] :=
    task_demand spec after (.start id)
  simp only [driveStep]
  split
  · exact singleton _
  · split
    · split
      · exact started _
      · exact singleton _
    · exact singleton _

/-- Actual reply preparation and resume retain initialized frames, captures and child readiness. -/
theorem prepared_configuration (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (raceFree : SourceScope.RaceFreeSource spec.root) (machine : NativeMachine)
    (id : FiberId) (token : Nat) (answer : Completion Val Err Defect FiberId Ann)
    (before : DriverState spec ((), ()) machine) (held : Configuration spec machine) :
    letI := evaluatorFor spec.root spec.table
    Configuration spec
      (driveStep (interpOf spec.root spec.table)
        {machine with state := (prepareAsyncAnswer (interpOf spec.root spec.table) machine id token answer).1}
        (.resume id token (prepareAsyncAnswer (interpOf spec.root spec.table) machine id token answer).2)
        [.drainDue]).1 := by
  letI := evaluatorFor spec.root spec.table
  have prepared := SourceScope.prepare_reply_at spec.root spec.table machine id token answer
  have changed := (configuration_edits spec).prepare machine id token answer held
  have owned : SourceScope.ConfigurationAt spec.root
      {machine with state := (prepareAsyncAnswer (interpOf spec.root spec.table) machine id token answer).1} := by
    refine ⟨before.1.2.fibers, before.1.2.races, ?_⟩
    rw [prepared.1]
    exact before.1.2.scopes
  apply changed.command spec fragment raceFree _ _ [.drainDue]
  · exact ⟨changed.scopes, before.2.fields rfl, owned, prepared.2,
      (Guard.AnswerDecision.prepareAsyncAnswer_shape spec.root spec.table machine id token answer).2.2,
      (by intro host impossible; cases impossible), trivial⟩
  · trivial

/-- The existing scheduler consumes the local command producer without a second command induction. -/
theorem coupled_decision (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (raceFree : SourceScope.RaceFreeSource spec.root)
    (step : letI := evaluatorFor spec.root spec.table
      ∀ tasks world machine command rest, machine.stuck = none →
        Lift.Guarded (DriverState spec) (DriverQueue spec) (DriverTasks spec) tasks world machine (command :: rest) →
        Lift.Guarded (fun (_ : Unit) => Configuration spec) (fun _ => QueueAt spec)
          (fun _ _ _ => True) tasks () machine (command :: rest) →
        Lift.Guarded (fun (_ : Unit) => Configuration spec) (fun _ => QueueAt spec)
          (fun _ _ _ => True) tasks ()
          (driveStep (interpOf spec.root spec.table) machine command rest).1
          (driveStep (interpOf spec.root spec.table) machine command rest).2) :
    letI := evaluatorFor spec.root spec.table
    Lift.CoupledDecision (p := Lift.unitOrder) (interp := interpOf spec.root spec.table)
      (J := DriverState spec) (I := DriverQueue spec) (O := DriverTasks spec) (A := fun _ _ _ => True)
      (P := fun _ => Configuration spec) (Q := fun _ => QueueAt spec) (R := fun _ _ _ => True) := by
  letI := evaluatorFor spec.root spec.table
  have edits := configuration_edits spec
  refine {
    step := ?_, nil := fun _ _ => trivial, drain := ?_, ran := ?_, task := ?_, skip := fun _ _ _ _ _ => trivial,
    clockNone := ?_, clockSome := ?_, evaluate := ?_, yield := ?_, interrupt := ?_, middleware := ?_, answer := ?_ }
  · intro tasks world extra machine command rest running base held
    cases extra
    exact ⟨(), trivial, step tasks world machine command rest running base held⟩
  · intro world extra machine owner fiber base held lookup
    exact ⟨edits.drain machine owner fiber held lookup, trivial⟩
  · intro world extra machine owner task base held
    exact edits.ran machine owner task held
  · intro world extra machine owner task tasks base held running reserved pending
    exact ⟨task_demand spec _ task, trivial⟩
  · intro world extra machine millis state base held running clock
    have after := edits.clock machine millis held running
    rw [clock] at after
    exact ⟨(), trivial, after⟩
  · intro world extra machine millis owed state base held running clock
    have after := edits.clock machine millis held running
    rw [clock] at after
    exact ⟨(), trivial, edits.owed _ owed after, fun _ => due_demand spec _ [owed]⟩
  · intro world extra machine id base held running
    exact task_demand spec machine (.start id)
  · intro world extra machine id verdict base held
    exact edits.yield machine id verdict held
  · intro world extra machine who reason target fiber base held lookup
    exact edits.interrupt machine who reason target fiber held lookup
  · intro world extra machine base held
    exact edits.middleware machine held
  · intro world extra machine id token answer base held running admitted
    exact ⟨(), trivial, prepared_configuration spec fragment raceFree machine id token answer base held,
      fun _ => ⟨resume_demand spec _ id token _, trivial⟩⟩

/-- The full initialized driver is the existing source driver times its actual coupled command fact. -/
theorem decision_lift_of_step (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (raceFree : SourceScope.RaceFreeSource spec.root)
    (step : letI := evaluatorFor spec.root spec.table
      ∀ tasks world machine command rest, machine.stuck = none →
        Lift.Guarded (DriverState spec) (DriverQueue spec) (DriverTasks spec) tasks world machine (command :: rest) →
        Lift.Guarded (fun (_ : Unit) => Configuration spec) (fun _ => QueueAt spec)
          (fun _ _ _ => True) tasks () machine (command :: rest) →
        Lift.Guarded (fun (_ : Unit) => Configuration spec) (fun _ => QueueAt spec)
          (fun _ _ _ => True) tasks ()
          (driveStep (interpOf spec.root spec.table) machine command rest).1
          (driveStep (interpOf spec.root spec.table) machine command rest).2) :
    letI := evaluatorFor spec.root spec.table
    Lift.DecisionLift (Lift.pairOrder (Lift.pairOrder Lift.unitOrder Lift.unitOrder) Lift.unitOrder)
      (interpOf spec.root spec.table)
      (fun _ machine => DriverState spec ((), ()) machine ∧ Configuration spec machine)
      (fun _ machine commands => DriverQueue spec ((), ()) machine commands ∧ QueueAt spec machine commands)
      (fun _ machine tasks => DriverTasks spec ((), ()) machine tasks ∧ True) (fun _ _ _ => True) := by
  letI := evaluatorFor spec.root spec.table
  exact (source_parked_lift spec.root fragment spec.table).withCoupledFact (coupled_decision spec fragment raceFree step)
end Effect4.Program.AnswerSlots.Initialized
