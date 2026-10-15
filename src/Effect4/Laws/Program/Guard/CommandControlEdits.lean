import Effect4.Laws.Program.Guard.NativeStateLinks
import Effect4.Laws.Machine.EditObserverWords

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: the initialized command queue retains its addressed source and drained stack.
Consumer: both crew log histories through Initialized.QueueAt.command.
The existing observer and scheduler paths supply the actual edits and produced commands.
These observations establish no source admission or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.Guard.CommandControl
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.NativeStateLinks

/-- Unchanged fiber rows keep both command observations. -/
theorem same {before after : NativeMachine} (fibers : after.fibers = before.fibers) :
    CommandControlsPreserved before after := by
  have lookup (id : FiberId) : after.fiber? id = before.fiber? id := by
    simp only [RunMachine.fiber?, fibers]
  exact ⟨fun id old found running parked => ⟨old, (lookup id).trans found, running, parked, rfl, fun h => h⟩,
    fun id old found exited => ⟨old, (lookup id).trans found, exited⟩⟩

/-- The observation composes along an existing edit path. -/
theorem trans {before middle after : NativeMachine}
    (first : CommandControlsPreserved before middle) (last : CommandControlsPreserved middle after) :
    CommandControlsPreserved before after := by
  constructor
  · intro id old found running parked
    obtain ⟨next, seen, run, park, current, empty⟩ := first.active id old found running parked
    obtain ⟨final, finalFound, finalRun, finalPark, finalCurrent, finalEmpty⟩ := last.active id next seen run park
    exact ⟨final, finalFound, finalRun, finalPark, finalCurrent.trans current, fun h => finalEmpty (empty h)⟩
  · intro id old found exited
    obtain ⟨next, seen, exit⟩ := first.exited id old found exited
    exact last.exited id next seen exit

/-- A metadata update retains the exact current and saved frame observations. -/
theorem update (before : NativeMachine) (target : FiberId) (old next : NFiber)
    (found : before.fiber? target = some old) (key : next.id = old.id)
    (frame : next.frame = old.frame) (parked : next.parked = old.parked)
    (running : next.running = old.running) (exit : next.exit = old.exit) :
    CommandControlsPreserved before (before.update next) := by
  have found' : before.fiber? old.id = some old := by
    simpa only [fiber_id_of_lookup found] using found
  apply controls_of_full
  · exact controlsPreserved_update_fields found' next
      ⟨key.symm, parked.symm, (congrArg FrameFiber.current frame).symm⟩ exit
      (fun run => running.trans run)
  · exact emptyStacks_update found' next key (fun empty => (congrArg FrameFiber.stack frame).trans empty)

/-- A producer word composes command observations without another interpreter induction. -/
theorem path {before after : NativeMachine} {word}
    (steps : Effect4.Contracts.Path (fun before after _ => CommandControlsPreserved before after)
      before after (word : List (Edit EffName EffThunk Val Err Defect FiberId Ann Ctx Stores NCode
        (FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)))) :
    CommandControlsPreserved before after := by
  induction steps with
  | nil => exact same rfl
  | cons first rest ih => exact trans first ih

/-- Actual interruption edits retain each active source head and every empty saved suffix. -/
theorem interrupts_path (root : NativeEff) (table : RowTable) (who : FiberId)
    (extra : ReasonAnnotations Ann) (targets : List FiberId) (acc : NativeMachine × List NCmd) :
    Effect4.Contracts.Path (fun before after _ => CommandControlsPreserved before after) acc.1
      (interruptEach (interpOf root table) who extra targets acc).1
      (Edits.interruptWords (interpOf root table) who extra targets acc) := by
  apply Edits.interrupts_path
  intro target held
  apply Edits.interrupt_path
  · intro machine target old found
    exact commandControls_interruptRecord root table
      (by simpa only [fiber_id_of_lookup found] using found) (some who) extra
  · intro machine target
    exact same rfl

/-- Observer callbacks introduce only evaluation or reply commands. -/
def Ordinary (command : NCmd) : Prop :=
  (∃ id, command = .evaluate id) ∨ ∃ id token code, command = .resume id token code

/-- One existing observer path supplies the active-control observation and its produced command form. -/
theorem observer (root : NativeEff) (table : RowTable) (id : FiberId) (exit : ExitV)
    (acc : NativeMachine × List NCmd) (observed : Observer) :
    CommandControlsPreserved acc.1 (fireObserver (interpOf root table) id exit acc observed).1 ∧
      ∀ command ∈ (fireObserver (interpOf root table) id exit acc observed).2,
        command ∈ acc.2 ∨ Ordinary command := by
  have produced := Edits.observer_producer_path_controls
    (Edge := fun before after _ => CommandControlsPreserved before after)
    (interpOf root table) (fun _ => 0) Ordinary id exit acc observed
    (fun machine target old next found key frame _ parked _ running _ _ exited _ =>
      update machine target old next found key frame parked running exited)
    (fun machine target observer _ => (Links.observer machine target observer).controls)
    (fun _ _ _ => same rfl) (fun _ _ _ => same rfl) (fun _ _ _ => same rfl)
    (fun _ _ _ _ _ _ => same rfl) (fun _ _ _ _ _ => same rfl)
    (fun _ _ _ _ => same rfl)
    (interrupts_path root table)
    (fun target => ⟨rfl, .inl ⟨target, rfl⟩⟩)
    (fun waiter token mode _ => ⟨rfl, .inr ⟨waiter, token, _, rfl⟩⟩)
    (fun race host token cleanup accepted _ => ⟨rfl, .inr ⟨host, token, _, rfl⟩⟩)
    (fun waiter token fiber pending exits _ _ _ _ => ⟨rfl, .inr ⟨waiter, token, _, rfl⟩⟩)
  exact ⟨path produced.1, produced.2.2⟩

/-- Posting a task changes dispatcher metadata without changing active source code. -/
theorem post_path (machine : NativeMachine) (owner : FiberId) (priority : Nat) (task : NTask) :
    Effect4.Contracts.Path (fun before after _ => CommandControlsPreserved before after) machine
      (machine.postTask owner priority task) (Edits.postTaskWord machine owner priority task) := by
  apply Edits.postTask_path
  · intro old found
    exact update machine owner old _ found rfl rfl rfl rfl rfl
  · exact fun _ => same rfl
  · exact fun _ => same rfl
  · exact same rfl

/-- Due-work draining reads the same scheduler edit path. -/
theorem drain (machine : NativeMachine) (owed : List (Owed NCode)) :
    CommandControlsPreserved machine (drainOwed machine owed).1 :=
  path (Edits.drain_path post_path machine owed)

end Effect4.Program.Guard.CommandControl
