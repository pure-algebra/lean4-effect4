import Effect4.Laws.Program.AnswerSlots.AllocationSettlement

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: pending allocation command and outside-decision interruption.
The actual interrupted root retains its exact heap and pending saved reply suffix.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Updating a checked pending row retains the other actual stored rows. -/
theorem PendingConfiguration.update (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine)
    (fiber : SourceScope.SourceFiber)
    (frame : FrameAt spec fragment ⟨fiber.id, machine.state, false⟩ fiber.frame)
    (waits : PendingWaits spec fragment ⟨fiber.id, machine.state, false⟩ fiber)
    (children : fiber.children = []) (observers : fiber.observers = []) (replies : Replies fiber.dispatcher)
    (recorded : CleanRecorded fiber.frame) :
    PendingConfiguration spec fragment (machine.update fiber) := by
  refine ⟨before.heap, ?_, ?_, ?_, ?_, before.counter, ?_, ?_, before.deferred⟩
  · intro row member
    obtain ⟨old, present, same⟩ := List.mem_map.mp member
    rw [← same]
    change FrameAt spec fragment ⟨(if old.id = fiber.id then fiber else old).id, machine.state, false⟩
      (if old.id = fiber.id then fiber else old).frame
    split
    · exact frame
    · exact before.frames old present
  · intro row member
    obtain ⟨old, present, same⟩ := List.mem_map.mp member
    rw [← same]
    change PendingWaits spec fragment ⟨(if old.id = fiber.id then fiber else old).id, machine.state, false⟩
      (if old.id = fiber.id then fiber else old)
    split
    · exact waits
    · exact before.waits old present
  · intro row member
    obtain ⟨old, present, same⟩ := List.mem_map.mp member
    rw [← same]
    change (if old.id = fiber.id then fiber else old).children = []
    split
    · exact children
    · exact before.childless old present
  · intro row member
    obtain ⟨old, present, same⟩ := List.mem_map.mp member
    rw [← same]
    change (if old.id = fiber.id then fiber else old).observers = []
    split
    · exact observers
    · exact before.unobserved old present
  · intro row member
    obtain ⟨old, present, same⟩ := List.mem_map.mp member
    rw [← same]
    change Replies (if old.id = fiber.id then fiber else old).dispatcher
    split
    · exact replies
    · exact before.replies old present

  · intro row member
    obtain ⟨old, present, same⟩ := List.mem_map.mp member
    rw [← same]
    change CleanRecorded (if old.id = fiber.id then fiber else old).frame
    split
    · exact recorded
    · exact before.recorded old present

/-- An actual interrupt keeps the saved parked suffix or removes the park. -/
theorem PendingWaits.interruption (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (world : World) (fiber : SourceScope.SourceFiber) (cause : CauseV)
    (waits : PendingWaits spec fragment world fiber) :
    PendingWaits spec fragment world (interruptWithCause cause fiber).1 := by
  unfold interruptWithCause
  dsimp only
  repeat' split
  all_goals dsimp only [PendingWaits] at waits ⊢
  all_goals aesop (add safe apply [waits])

/-- The actual interrupt edit retains the whole pending machine configuration. -/
theorem PendingConfiguration.interruption (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine)
    (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers) (cause : CauseV)
    (incoming : CleanCause cause) :
    PendingConfiguration spec fragment (machine.update (interruptWithCause cause fiber).1) := by
  have id : (interruptWithCause cause fiber).1.id = fiber.id := by
    unfold interruptWithCause
    dsimp only
    repeat' split
    all_goals rfl
  apply PendingConfiguration.update spec fragment machine before
  · rw [id]
    exact FrameAt.interruption spec fragment ⟨fiber.id, machine.state, false⟩ fiber cause (before.frames fiber member)
  · rw [id]
    exact PendingWaits.interruption spec fragment _ fiber cause (before.waits fiber member)
  · have same : (interruptWithCause cause fiber).1.children = fiber.children := by
      unfold interruptWithCause
      dsimp only
      repeat' split
      all_goals rfl
    exact same.trans (before.childless fiber member)
  · have same : (interruptWithCause cause fiber).1.observers = fiber.observers := by
      unfold interruptWithCause
      dsimp only
      repeat' split
      all_goals rfl
    exact same.trans (before.unobserved fiber member)
  · have same : (interruptWithCause cause fiber).1.dispatcher = fiber.dispatcher := by
      unfold interruptWithCause
      dsimp only
      repeat' split
      all_goals rfl
    rw [same]
    exact before.replies fiber member
  · exact CleanRecorded.interruption fiber cause incoming (before.recorded fiber member)

end Effect4.Program.AnswerSlots.AllocationAdapter
