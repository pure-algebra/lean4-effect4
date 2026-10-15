import Effect4.Laws.Program.AnswerSlots.InitializedAdminProduction

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: the initialized machine and its actual pending commands advance jointly.
Reach: source and guard authority, administrative source heads, drained finish suffixes and tracked child readiness.
Limit: no progress, arbitrary reply admission or external implementation agreement follows.
Consumer: both crew log histories through the shared initialized decision lift.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Each queued command carries precisely the extra observations its actual consumer reads. -/
def CommandDemand (spec : Spec) (machine : NativeMachine) (command : Guard.NCmd) : Prop :=
  AdminHead machine command ∧ FinishEmpty machine command ∧ TrackDemand spec machine command

/-- The pending command word retains its administrative and finish observations at the actual machine. -/
def QueueAt (spec : Spec) (machine : NativeMachine) (commands : List Guard.NCmd) : Prop :=
  ∀ command ∈ commands, CommandDemand spec machine command

/-- Drained tasks introduce only ordinary evaluation, reply and wake commands. -/
def DrainedTasks (_spec : Spec) (_machine : NativeMachine) (_tasks : List Guard.NTask) : Prop := True

/-- A simple command that neither finishes nor tracks a child needs no extra observation. -/
theorem ordinary_demand (spec : Spec) (machine : NativeMachine) (command : Guard.NCmd)
    (localFree : ∀ host, ¬ Guard.ReturnCommands.Local host command)
    (finishFree : ∀ host exit, command ≠ .finish host exit)
    (trackFree : ∀ parent child, command ≠ .trackChild parent child) : CommandDemand spec machine command := by
  refine ⟨?_, ?_, ?_⟩
  · intro host isLocal
    exact (localFree host isLocal).elim
  · cases command <;> simp only [FinishEmpty]
    rename_i host exit
    exact (finishFree host exit rfl).elim
  · cases command <;> simp only [TrackDemand]
    rename_i parent child
    exact (trackFree parent child rfl).elim

/-- The empty command word has no outstanding demand. -/
theorem QueueAt.nil (spec : Spec) (machine : NativeMachine) : QueueAt spec machine [] := by
  intro command member
  cases member

/-- A retained suffix keeps each of its actual command observations. -/
theorem QueueAt.tail {spec : Spec} {machine : NativeMachine} {command : Guard.NCmd} {rest : List Guard.NCmd}
    (held : QueueAt spec machine (command :: rest)) : QueueAt spec machine rest :=
  fun next member => held next (List.mem_cons_of_mem command member)

/-- Joined command words need exactly their two actual queue certificates. -/
theorem QueueAt.append {spec : Spec} {machine : NativeMachine} {first last : List Guard.NCmd}
    (front : QueueAt spec machine first) (back : QueueAt spec machine last) : QueueAt spec machine (first ++ last) := by
  intro command member
  rcases List.mem_append.mp member with earlier | later
  · exact front command earlier
  · exact back command later

/-- Every command introduced by a drained scheduler task has no administrative or finish demand. -/
theorem task_demand (spec : Spec) (machine : NativeMachine) (task : Guard.NTask) :
    QueueAt spec machine (taskCmds task) := by
  have pair (first : Guard.NCmd) (front : CommandDemand spec machine first)
      (back : CommandDemand spec machine .drainDue) : QueueAt spec machine [first, .drainDue] := by
    intro command member
    rcases List.mem_cons.mp member with same | rest
    · subst command
      exact front
    · have same := List.mem_singleton.mp rest
      subst command
      exact back
  cases task <;> apply pair
  all_goals
    exact ordinary_demand spec machine _ (fun _ impossible => impossible.elim)
      (fun _ _ same => by cases same) (fun _ _ same => by cases same)
end Effect4.Program.AnswerSlots.Initialized
