import Effect4.Laws.Program.AnswerSlots.AllocationInterruption

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the actual pending allocation administrative and decision driver.
Untouched frame, park and ownership fields retain the exact pending row observation.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Pending rows observe only these immutable fields during administration. -/
def SamePendingRow (before after : SourceScope.SourceFiber) : Prop :=
  after.id = before.id ∧ after.frame = before.frame ∧ after.parked = before.parked ∧
    after.children = before.children ∧ after.observers = before.observers ∧ after.dispatcher = before.dispatcher

/-- Equal allocation counts and references retain the actual parked reply demand. -/
theorem PendingWaits.store_fields (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (owner : FiberId) (before after : Stores) (fiber : SourceScope.SourceFiber)
    (waits : PendingWaits spec fragment ⟨owner, before, false⟩ fiber)
    (refs : after.refs = before.refs)
    (deferred : after.deferreds.cells.length = before.deferreds.cells.length) :
    PendingWaits spec fragment ⟨owner, after, false⟩ fiber := by
  intro parked
  obtain ⟨output, demand, saved⟩ := waits parked
  have future : Future ⟨owner, before, false⟩ ⟨owner, after, false⟩ :=
    ⟨rfl, Nat.le_of_eq (congrArg List.length refs.symm), Nat.le_of_eq deferred.symm, fun pending => pending⟩
  refine ⟨output, ⟨phase_future spec _ _ future demand.phase, ?_, rfl⟩, ?_⟩
  · change after.refs = Initialization.values spec.initialization after.refs.length
    rw [refs]
    exact demand.contents
  · have moved := path_future spec fragment _ _ future _ _ fiber.frame.stack saved
    change Effect4.Contracts.Path (Edge spec fragment ⟨owner, after, false⟩)
      (.yielded after.refs.length after.deferreds.cells.length) output fiber.frame.stack
    rw [refs, deferred]
    exact moved

/-- Exact allocation fields and the actual row projection transfer the whole pending configuration. -/
theorem PendingConfiguration.transfer (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (before after : NativeMachine) (held : PendingConfiguration spec fragment before)
    (refs : after.state.refs = before.state.refs)
    (deferred : after.state.deferreds.cells.length = before.state.deferreds.cells.length)
    (counter : after.nextId = before.nextId)
    (rows : ∀ row ∈ after.fibers, ∃ old ∈ before.fibers, SamePendingRow old row) :
    PendingConfiguration spec fragment after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, counter.trans held.counter, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [refs]; exact held.heap.1
    · rw [refs, deferred]; exact held.heap.2
  · intro row member
    obtain ⟨old, present, id, frame, park, children, observers, dispatcher⟩ := rows row member
    have moved := FrameAt.store_fields spec fragment old.id before.state after.state old.frame
      ⟨held.frames old present, held.heap⟩ refs deferred
    change FrameAt spec fragment ⟨row.id, after.state, false⟩ row.frame
    rw [id, frame]
    exact moved.1
  · intro row member
    obtain ⟨old, present, id, frame, park, children, observers, dispatcher⟩ := rows row member
    have moved := PendingWaits.store_fields spec fragment old.id before.state after.state old
      (held.waits old present) refs deferred
    intro parked
    have oldParked : old.parked ≠ .notParked := fun same => parked (park.trans same)
    obtain ⟨output, demand, saved⟩ := moved oldParked
    refine ⟨output, ?_, ?_⟩
    · rw [id]; exact demand
    · rw [id, frame]; exact saved
  · intro row member
    obtain ⟨old, present, id, frame, park, children, observers, dispatcher⟩ := rows row member
    exact children.trans (held.childless old present)
  · intro row member
    obtain ⟨old, present, id, frame, park, children, observers, dispatcher⟩ := rows row member
    exact observers.trans (held.unobserved old present)
  · intro row member
    obtain ⟨old, present, id, frame, park, children, observers, dispatcher⟩ := rows row member
    rw [dispatcher]
    exact held.replies old present
/-- Administrative store hooks preserve the entire pending configuration at equal allocation fields. -/
theorem PendingConfiguration.store_fields (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (state : Stores) (held : PendingConfiguration spec fragment machine)
    (refs : state.refs = machine.state.refs)
    (deferred : state.deferreds.cells.length = machine.state.deferreds.cells.length) :
    PendingConfiguration spec fragment {machine with state} := by
  apply PendingConfiguration.transfer spec fragment machine {machine with state} held refs deferred rfl
  intro row member
  exact ⟨row, member, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Effect4.Program.AnswerSlots.AllocationAdapter
