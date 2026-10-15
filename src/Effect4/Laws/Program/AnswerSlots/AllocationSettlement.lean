import Effect4.Laws.Program.AnswerSlots.AllocationNativeCut

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the common pending allocation command/history producer.
The actual native cut retains its joint pending configuration through settlement.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Machine fields outside the pending observation do not change its configuration. -/
theorem PendingConfiguration.fields (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (before after : NativeMachine) (held : PendingConfiguration spec fragment before)
    (state : after.state = before.state) (fibers : after.fibers = before.fibers)
    (counter : after.nextId = before.nextId) : PendingConfiguration spec fragment after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, counter.trans held.counter⟩
  · rw [state]; exact held.heap
  · intro row member
    rw [fibers] at member
    change FrameAt spec fragment ⟨row.id, after.state, false⟩ row.frame
    rw [state]; exact held.frames row member
  · intro row member
    rw [fibers] at member
    rw [state]; exact held.waits row member
  · intro row member
    rw [fibers] at member
    exact held.childless row member
  · intro row member
    rw [fibers] at member
    exact held.unobserved row member

/-- Settlement changes only the returned owner's administrative fiber fields. -/
theorem PendingNativeCut.replace (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (result : Moves.NIteration)
    (before : PendingConfiguration spec fragment machine) (member : fiber ∈ machine.fibers)
    (cut : PendingNativeCut spec fragment machine fiber result)
    (after : SourceScope.SourceFiber) (id : after.id = result.fiber.id)
    (frame : after.frame = result.fiber.frame) (children : after.children = result.fiber.children)
    (observers : after.observers = result.fiber.observers)
    (waits : PendingWaits spec fragment ⟨after.id, result.machine.state, false⟩ after) :
    PendingConfiguration spec fragment (result.machine.update after) := by
  have rows : ∀ row ∈ (result.machine.update after).fibers, row = after := by
    intro row present
    obtain ⟨old, present, same⟩ := List.mem_map.mp present
    rw [← same]
    change (if old.id = after.id then after else old) = after
    split
    · rfl
    · rename_i different
      have updated : old ∈ (result.machine.update result.fiber).fibers := by
        apply List.mem_map.mpr
        refine ⟨old, present, ?_⟩
        change (if old.id = result.fiber.id then result.fiber else old) = old
        rw [if_neg (fun equal => different (equal.trans id.symm))]
      have sameOld := PendingNativeCut.rows spec fragment machine fiber result cut old updated
      exact (different (sameOld ▸ id.symm)).elim
  refine ⟨cut.heap, ?_, ?_, ?_, ?_, cut.counter.trans before.counter⟩
  · intro row present
    rw [rows row present]
    change FrameAt spec fragment ⟨after.id, result.machine.state, false⟩ after.frame
    rw [id, frame]
    exact cut.flows.2.1
  · intro row present
    rw [rows row present]
    exact waits
  · intro row present
    rw [rows row present, children, cut.footprint.children]
    exact before.childless fiber member
  · intro row present
    rw [rows row present, observers, cut.footprint.observers]
    exact before.unobserved fiber member

/-- The actual pending native cut remains pending after all outcome dispositions. -/
theorem PendingNativeCut.settlement (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (result : Moves.NIteration)
    (before : PendingConfiguration spec fragment machine) (member : fiber ∈ machine.fibers)
    (cut : PendingNativeCut spec fragment machine fiber result) (id : FiberId) (rest : List SourceScope.SourceCommand) :
    PendingConfiguration spec fragment (settle id rest result).1 := by
  simp only [settle, cut.effects.1]
  have original := cut.configuration spec fragment machine fiber result before member
  have stopped : PendingConfiguration spec fragment
      (result.machine.update {result.fiber with running := false}) :=
    cut.replace spec fragment machine fiber result before member _ rfl rfl rfl rfl cut.waits
  have unparked : PendingConfiguration spec fragment
      (result.machine.update {result.fiber with parked := .notParked, pending := []}) :=
    cut.replace spec fragment machine fiber result before member _ rfl rfl rfl rfl
      (fun parked => (parked rfl).elim)
  cases outcome : result.outcome with
  | continue_ => simpa only [settleOutcome, outcome] using original
  | answered => simpa only [settleOutcome, outcome] using original
  | parked =>
    simp only [settleOutcome, outcome]
    split
    · exact unparked
    · exact stopped
  | commands => simpa only [settleOutcome, outcome] using original
  | finished exit => simpa only [settleOutcome, outcome] using original
  | stuck why =>
    simp only [settleOutcome, outcome]
    exact PendingConfiguration.fields spec fragment _ _ stopped rfl rfl rfl
/-- A real pending loop command settles in the same configuration or reaches actual application entry. -/
theorem pending_loop_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (before : PendingConfiguration spec fragment machine) (found : machine.fiber? fiber.id = some fiber)
    (unparked : fiber.parked = .notParked) (rest : List SourceScope.SourceCommand) :
    let result := iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding
    (PendingNativeCut spec fragment machine fiber result ∧
      PendingConfiguration spec fragment (settle fiber.id rest result).1) ∨
      EntryRun spec fragment machine fiber yielding result := by
  have member := RunMachine.mem_of_fiber? found
  obtain ⟨input, output, current, saved⟩ := before.frames fiber member
  rcases pending_iteration_cut_or_entry spec fragment machine fiber yielding input output current saved before.frames before.heap unparked with cut | entry
  · exact .inl ⟨cut, cut.settlement spec fragment machine fiber _ before member fiber.id rest⟩
  · exact .inr entry

end Effect4.Program.AnswerSlots.AllocationAdapter
