import Effect4.Laws.Program.ReleaseCustody.Sequencing
import Effect4.Laws.Program.Guard.NativeQueueTail

/-!
Concept: scope-lifetime-finalization R11, serving `ReleaseCustody.Execution.history`.
Consumers: native evaluator installation and command custody.
The existing command owner identifies the saved stack that an overwrite consumes.
GuardQueue's unique owners protect the unexecuted queue from a different owner's stack change.
These relations inspect actual machine fields and establish no history or progress alone.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.CommandStacks
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.Sequencing

/-- Local evaluation retains every old stored stack until its returned fiber is installed. -/
def StackLinks (before after : NativeMachine) : Prop :=
  ∀ id fiber, before.fiber? id = some fiber →
    ∃ next, after.fiber? id = some next ∧ next.frame.stack = fiber.frame.stack

/-- Installing a returned fiber may change only its owner's saved stack. -/
def StackLinksAway (owner : FiberId) (before after : NativeMachine) : Prop :=
  ∀ id fiber, id ≠ owner → before.fiber? id = some fiber →
    ∃ next, after.fiber? id = some next ∧ next.frame.stack = fiber.frame.stack

/-- An administrative overwrite has no pending scope-add callback; finish has consumed its stack. -/
def CommandFrames : NCmd → List NCode → Prop
  | .finish _ _, frames => frames = []
  | .afterInterrupt _ _ _, frames | .registrationDone _ _, frames
  | .raceCancel _ _ _ _ _, frames | .closeParAwait _ _ _, frames => NoAdd frames
  | _, _ => True

/-- An owned queued command retains the stack required by its eventual overwrite. -/
def QueueStable (machine : NativeMachine) (commands : List NCmd) : Prop :=
  ∀ command ∈ commands, ∀ owner, commandOwner machine command = some owner →
    ∀ fiber, machine.fiber? owner = some fiber → CommandFrames command fiber.frame.stack

theorem StackLinks.refl (m : NativeMachine) : StackLinks m m :=
  fun _ fiber found => ⟨fiber, found, rfl⟩

theorem StackLinks.trans {m n o : NativeMachine} (first : StackLinks m n)
    (second : StackLinks n o) : StackLinks m o := by
  intro id fiber found
  obtain ⟨middle, seen, kept⟩ := first id fiber found
  obtain ⟨last, final, same⟩ := second id middle seen
  exact ⟨last, final, same.trans kept⟩

theorem StackLinks.of_fibers {m n : NativeMachine} (same : n.fibers = m.fibers) :
    StackLinks m n := by
  intro id fiber found
  exact ⟨fiber, by simpa only [RunMachine.fiber?, same] using found, rfl⟩

theorem StackLinks.away {m n : NativeMachine} (kept : StackLinks m n) (owner : FiberId) :
    StackLinksAway owner m n := fun id fiber _ found => kept id fiber found

theorem StackLinksAway.trans {m n o : NativeMachine} {owner : FiberId}
    (first : StackLinksAway owner m n) (second : StackLinksAway owner n o) :
    StackLinksAway owner m o := by
  intro id fiber different found
  obtain ⟨middle, seen, kept⟩ := first id fiber different found
  obtain ⟨last, final, same⟩ := second id middle different seen
  exact ⟨last, final, same.trans kept⟩

/-- Updating one row leaves every differently owned stack unchanged. -/
theorem update_away (m : NativeMachine) (next : Guard.NFiber) :
    StackLinksAway next.id m (m.update next) := by
  intro id fiber different found
  refine ⟨fiber, ?_, rfl⟩
  rw [fiber_lookup_update, found, Option.map_some]
  rw [if_neg (fun equal => different ((fiber_id_of_lookup found).symm.trans equal))]

/-- Replacing fields outside the stack retains every existing stack. -/
theorem update_links (m : NativeMachine) (before next : Guard.NFiber)
    (found : m.fiber? next.id = some before) (stack : next.frame.stack = before.frame.stack) :
    StackLinks m (m.update next) := by
  intro id fiber seen
  by_cases same : id = next.id
  · subst id
    have equal : fiber = before := Option.some.inj (seen.symm.trans found)
    subst fiber
    exact ⟨next, fiber_lookup_update_self found next rfl, stack⟩
  · exact update_away m next id fiber same seen

/-- An administrative edit preserves all stored stacks when it preserves the edited stack. -/
theorem modify_links (m : NativeMachine) (id : FiberId) (edit : Guard.NFiber → Guard.NFiber)
    (key : ∀ fiber, (edit fiber).id = fiber.id)
    (stack : ∀ fiber, (edit fiber).frame.stack = fiber.frame.stack) :
    StackLinks m (m.modify id edit) := by
  unfold RunMachine.modify
  split
  · exact StackLinks.refl m
  · rename_i fiber found
    apply update_links m fiber (edit fiber)
    · rw [key, fiber_id_of_lookup found]
      exact found
    · exact stack fiber

/-- A newly appended row does not replace an existing row's saved stack. -/
theorem append_links (m : NativeMachine) (next : Guard.NFiber) :
    StackLinks m {m with fibers := m.fibers ++ [next]} := by
  intro id fiber found
  refine ⟨fiber, ?_, rfl⟩
  change List.find? _ (m.fibers ++ [next]) = some fiber
  unfold RunMachine.fiber? at found
  rw [List.find?_append, found]
  rfl

/-- Interrupt recording changes the current answer and flags, never the saved stack. -/
theorem interrupt_stack (root : NativeEff) (table : RowTable) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (fiber : Guard.NFiber) :
    (interruptRecord (interpOf root table) who extra fiber).1.frame.stack = fiber.frame.stack := by
  unfold interruptRecord interruptWithCause
  dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
    FiberCore.setDeferred, FiberCore.answerWith, FiberCore.failure, frameCore]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-- A recorded interruption retains every old saved stack. -/
theorem interrupt_links (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Guard.NFiber) (found : m.fiber? fiber.id = some fiber)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    StackLinks m (m.update (interruptRecord (interpOf root table) who extra fiber).1) := by
  apply update_links m fiber _
  · rw [interruptRecord_id]
    exact found
  · exact interrupt_stack root table who extra fiber

/-- An empty command suffix owes no stack condition. -/
theorem queue_nil (m : NativeMachine) : QueueStable m [] := by
  intro command member
  cases member

/-- Appending command lists combines their actual owner obligations. -/
theorem queue_append {m : NativeMachine} {front rest : List NCmd}
    (first : QueueStable m front) (last : QueueStable m rest) : QueueStable m (front ++ rest) := by
  intro command member
  rcases List.mem_append.mp member with before | after
  · exact first command before
  · exact last command after

/-- Removing the head retains every command obligation in the suffix. -/
theorem queue_tail {m : NativeMachine} {head : NCmd} {rest : List NCmd}
    (held : QueueStable m (head :: rest)) : QueueStable m rest :=
  fun command member => held command (List.mem_cons_of_mem head member)

/-- The head command's owner cannot own any later command. -/
theorem tail_owner_distinct (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (head : NCmd) (tail : List NCmd) (queue : GuardQueue root table m (head :: tail))
    (owner : FiberId) (owns : commandOwner m head = some owner)
    (command : NCmd) (member : command ∈ tail) (target : FiberId)
    (targets : commandOwner m command = some target) : target ≠ owner := by
  have unique := queue.owners
  rw [List.filterMap_cons, owns] at unique
  have fresh := (List.nodup_cons.mp unique).1
  intro same
  exact fresh (same ▸ List.mem_filterMap.mpr ⟨command, member, targets⟩)

/-- Moving stored stacks and race owners transports every outstanding command obligation. -/
theorem queue_transport (root : NativeEff) (table : RowTable) {m n : NativeMachine}
    {commands : List NCmd} (queue : GuardQueue root table m commands)
    (held : QueueStable m commands) (races : RaceHostsPreserved m n) (links : StackLinks m n) :
    QueueStable n commands := by
  intro command member owner owns fiber found
  have oldOwner := commandOwner_transport root table races command (queue.authority command member)
  rw [oldOwner] at owns
  obtain ⟨old, seen, _, _⟩ := commandAuthority_owner_active root table m command owner
    (queue.authority command member) owns
  obtain ⟨next, present, stack⟩ := links owner old seen
  have equal : next = fiber := Option.some.inj (present.symm.trans found)
  subst fiber
  rw [stack]
  exact held command member owner owns old seen

/-- Unique command ownership protects the tail when the active owner's stack changes. -/
theorem queue_tail_transport (root : NativeEff) (table : RowTable) {m n : NativeMachine}
    (head : NCmd) (tail : List NCmd) (queue : GuardQueue root table m (head :: tail))
    (held : QueueStable m tail) (owner : FiberId) (owns : commandOwner m head = some owner)
    (races : RaceHostsPreserved m n) (links : StackLinksAway owner m n) : QueueStable n tail := by
  intro command member target targets fiber found
  have authority := queue.authority command (List.mem_cons_of_mem head member)
  rw [commandOwner_transport root table races command authority] at targets
  have different := tail_owner_distinct root table m head tail queue owner owns command member target targets
  obtain ⟨old, seen, _, _⟩ := commandAuthority_owner_active root table m command target authority targets
  obtain ⟨next, present, stack⟩ := links target old different seen
  have equal : next = fiber := Option.some.inj (present.symm.trans found)
  subst fiber
  rw [stack]
  exact held command member target targets old seen

end Effect4.Program.ReleaseCustody.CommandStacks
