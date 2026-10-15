import Effect4.Laws.Program.AnswerSlots.AllocationDriver

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the shared allocation driver and its application histories.
Actual command authority supplies the running, unparked native owner.
Only the real source-entry branches call the application's joint postcondition.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program
universe u

/-- One pending command retains initialization or enters the application at its real native cut. -/
theorem pending_command_step {V : Type u} (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (P : V → NativeMachine → Prop) (Q : V → NativeMachine → List Guard.NCmd → Prop)
    (R : V → NativeMachine → List Guard.NTask → Prop)
    (machine : NativeMachine) (command : Guard.NCmd) (rest : List Guard.NCmd) (tasks : List Guard.NTask)
    (before : PendingConfiguration spec fragment machine) (allowed : PendingCommand command)
    (queue : PendingQueue rest) (snapshot : PendingSnapshot tasks)
    (authority : Guard.CommandAuthority spec.root spec.table machine command)
    (enter_iteration : ∀ fiber yielding result, machine.fiber? fiber.id = some fiber →
      command = .loop fiber.id yielding → EntryRun spec fragment machine fiber yielding result →
      ∃ world, Lift.Guarded P Q R tasks world (settle fiber.id rest result).1 (settle fiber.id rest result).2)
    (enter_native : ∀ fiber yielding, machine.fiber? fiber.id = some fiber →
      command = .deliver fiber.id yielding → EntryAt spec fragment machine fiber →
      ∃ world, Lift.Guarded P Q R tasks world
        (settle fiber.id rest (evaluateNative spec.root machine fiber yielding spec.table)).1
        (settle fiber.id rest (evaluateNative spec.root machine fiber yielding spec.table)).2) :
    letI := evaluatorFor spec.root spec.table
    ∃ next, Lift.Guarded (AttachedState spec fragment P) (AttachedQueue Q) (AttachedTasks R)
      tasks next (driveStep (interpOf spec.root spec.table) machine command rest).1
      (driveStep (interpOf spec.root spec.table) machine command rest).2 := by
  letI := evaluatorFor spec.root spec.table
  by_cases fixed : AnswerFlow.ghostAdvancing command = false
  · have permission := PendingCommand.fixed command allowed fixed
    exact ⟨none, before.fixed spec fragment machine command rest permission,
      fun _ => ⟨pending_fixed_queue spec fragment machine command rest before permission queue, snapshot⟩⟩
  · cases command <;> simp only [PendingCommand] at allowed
    all_goals simp only [AnswerFlow.ghostAdvancing, not_true_eq_false] at fixed
    case loop id yielding =>
      obtain ⟨fiber, found, running, unparked⟩ := authority
      have idEq := Guard.fiber_id_of_lookup found
      have ownLookup : machine.fiber? fiber.id = some fiber := by rw [idEq]; exact found
      simp only [driveStep, found]
      rw [← idEq]
      rcases pending_loop_or_entry spec fragment machine fiber yielding before ownLookup unparked rest with pending | entry
      · exact ⟨none, pending.2, fun _ => ⟨pending.1.queue spec fragment machine fiber _ fiber.id rest queue, snapshot⟩⟩
      · obtain ⟨world, post⟩ := enter_iteration fiber yielding _ ownLookup (congrArg (fun key => Cmd.loop key yielding) idEq.symm) entry
        exact ⟨some world, post⟩
    case deliver id yielding =>
      obtain ⟨fiber, found, running, unparked⟩ := authority
      have idEq := Guard.fiber_id_of_lookup found
      have ownLookup : machine.fiber? fiber.id = some fiber := by rw [idEq]; exact found
      obtain ⟨input, output, current, saved⟩ := before.frames fiber (RunMachine.mem_of_fiber? found)
      simp only [driveStep, found]
      rw [← idEq]
      rcases pending_native_cut_or_entry spec fragment machine fiber yielding input output current saved before.frames before.heap unparked with cut | entry
      · exact ⟨none, cut.settlement spec fragment machine fiber _ before (RunMachine.mem_of_fiber? found) fiber.id rest,
          fun _ => ⟨cut.queue spec fragment machine fiber _ fiber.id rest queue, snapshot⟩⟩
      · obtain ⟨point, kind, same, atEntry⟩ := entry
        subst input
        obtain ⟨world, post⟩ := enter_native fiber yielding ownLookup (congrArg (fun key => Cmd.deliver key yielding) idEq.symm)
          ⟨point, output, same, atEntry, saved⟩
        exact ⟨some world, post⟩
end Effect4.Program.AnswerSlots.AllocationAdapter

namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program
universe u v

/-- Concrete entry callbacks complete the common pending command and outside-decision producer. -/
theorem coupled_decision_of_entry {W : Type v} {V : Type u} (spec : Spec)
    (fragment : SourceScope.Fragment spec.root) (p : Effect4.Laws.Effects.WorldOrder V)
    (J : W → NativeMachine → Prop) (I : W → NativeMachine → List Guard.NCmd → Prop)
    (O : W → NativeMachine → List Guard.NTask → Prop)
    (A : W → NativeMachine → RunDecision EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (P : V → NativeMachine → Prop) (Q : V → NativeMachine → List Guard.NCmd → Prop)
    (R : V → NativeMachine → List Guard.NTask → Prop)
    (active : letI := evaluatorFor spec.root spec.table
      Lift.CoupledDecision (p := p) (interp := interpOf spec.root spec.table)
        (J := J) (I := I) (O := O) (A := A) (P := P) (Q := Q) (R := R))
    (authority : ∀ world machine commands, I world machine commands →
      ∀ command ∈ commands, Guard.CommandAuthority spec.root spec.table machine command)
    (enter_iteration : ∀ tasks world machine command rest,
      Lift.Guarded J I O tasks world machine (command :: rest) →
      PendingConfiguration spec fragment machine → PendingQueue rest → PendingSnapshot tasks →
      ∀ fiber yielding result, machine.fiber? fiber.id = some fiber → command = .loop fiber.id yielding →
      EntryRun spec fragment machine fiber yielding result →
      ∃ next, Lift.Guarded P Q R tasks next (settle fiber.id rest result).1 (settle fiber.id rest result).2)
    (enter_native : ∀ tasks world machine command rest,
      Lift.Guarded J I O tasks world machine (command :: rest) →
      PendingConfiguration spec fragment machine → PendingQueue rest → PendingSnapshot tasks →
      ∀ fiber yielding, machine.fiber? fiber.id = some fiber → command = .deliver fiber.id yielding →
      EntryAt spec fragment machine fiber →
      ∃ next, Lift.Guarded P Q R tasks next
        (settle fiber.id rest (evaluateNative spec.root machine fiber yielding spec.table)).1
        (settle fiber.id rest (evaluateNative spec.root machine fiber yielding spec.table)).2) :
    letI := evaluatorFor spec.root spec.table
    Lift.CoupledDecision (p := attachmentOrder V) (interp := interpOf spec.root spec.table)
      (J := J) (I := I) (O := O) (A := A)
      (P := AttachedState spec fragment P) (Q := AttachedQueue Q) (R := AttachedTasks R) := by
  letI := evaluatorFor spec.root spec.table
  apply coupled_decision spec fragment p J I O A P Q R active
  intro tasks world machine command rest running base held
  have full : PendingQueue (command :: rest) := (held.2 running).1
  have tail : PendingQueue rest := fun next member => full next (.tail _ member)
  have snapshot : PendingSnapshot tasks := (held.2 running).2
  exact pending_command_step spec fragment P Q R machine command rest tasks held.1
    (full command (.head _)) tail snapshot
    (authority world machine _ (base.2 running).1 command (.head _))
    (enter_iteration tasks world machine command rest base held.1 tail snapshot)
    (enter_native tasks world machine command rest base held.1 tail snapshot)
end Effect4.Program.AnswerSlots.AllocationAdapter
