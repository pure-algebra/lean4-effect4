import Effect4.Laws.Program.AnswerSlots.InitializedDecision
import Effect4.Laws.Program.AnswerSlots.InitializedQueueAdmin
import Effect4.Laws.Program.AnswerSlots.InitializedQueueDynamic

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual initialized crew histories retain current values, captures and pending demands together.
Consumers: Workers.Assertions.logs_step and QueueWorkers.Assertions.logs_history.
Reach: every budget and admitted decision of the certified lexical source without races.
No progress, fairness or host agreement follows.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Every actual command advances the machine and pending initialized assertions together. -/
theorem command_guarded (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (raceFree : SourceScope.RaceFreeSource spec.root) :
    letI := evaluatorFor spec.root spec.table
    ∀ tasks world machine command rest, machine.stuck = none →
      Lift.Guarded (DriverState spec) (DriverQueue spec) (DriverTasks spec) tasks world machine (command :: rest) →
      Lift.Guarded (fun (_ : Unit) => Configuration spec) (fun _ => QueueAt spec)
        (fun _ _ _ => True) tasks () machine (command :: rest) →
      Lift.Guarded (fun (_ : Unit) => Configuration spec) (fun _ => QueueAt spec)
        (fun _ _ _ => True) tasks ()
        (driveStep (interpOf spec.root spec.table) machine command rest).1
        (driveStep (interpOf spec.root spec.table) machine command rest).2 := by
  letI := evaluatorFor spec.root spec.table
  intro tasks world machine command rest running base held
  have queue := (base.2 running).1.1.1
  have source := (base.2 running).1.2
  have pending := (held.2 running).1
  have head := pending command (List.mem_cons_self ..)
  have permission : CommandPremises spec machine command :=
    ⟨held.1.scopes, base.1.2, base.1.1.2, source command (List.mem_cons_self ..),
      queue.codeSites command (List.mem_cons_self ..),
      admin_of_head spec machine command held.1.frames head.1,
      terminal_of_empty spec machine command held.1.children head.2.1⟩
  refine ⟨held.1.command spec fragment raceFree machine command rest permission head.2.2, fun _ => ⟨?_, trivial⟩⟩
  apply QueueAt.command_of_evaluation spec raceFree machine command rest base.1.1.2 base.1.1.1 queue pending
  · intro id yielding same
    subst command
    exact QueueAt.command_loop spec fragment machine id yielding rest held.1 base.1.1.1 queue pending
  · intro id yielding same
    subst command
    exact QueueAt.command_deliver spec fragment machine id yielding rest held.1 base.1.1.1 queue pending

/-- The initialized driver consumes proved command producers and the existing decision lift. -/
theorem decision_lift (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (raceFree : SourceScope.RaceFreeSource spec.root) :
    letI := evaluatorFor spec.root spec.table
    Lift.DecisionLift (Lift.pairOrder (Lift.pairOrder Lift.unitOrder Lift.unitOrder) Lift.unitOrder)
      (interpOf spec.root spec.table)
      (fun _ machine => DriverState spec ((), ()) machine ∧ Configuration spec machine)
      (fun _ machine commands => DriverQueue spec ((), ()) machine commands ∧ QueueAt spec machine commands)
      (fun _ machine tasks => DriverTasks spec ((), ()) machine tasks ∧ True) (fun _ _ _ => True) :=
  decision_lift_of_step spec fragment raceFree (command_guarded spec fragment raceFree)

end Effect4.Program.AnswerSlots.Initialized
