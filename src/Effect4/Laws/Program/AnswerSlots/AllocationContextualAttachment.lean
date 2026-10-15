import Effect4.Laws.Program.AnswerSlots.AllocationAttachment

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: Atomic, Queue and Timeout contextual source-entry activation.
Actual entry retains external counter, queue and detached-task authority through an explicit admission.
The application returns one proof world for its whole actual native postcondition.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program
universe u

/-- A source-entry native producer may read the caller's actual joint machine and queue authority. -/
def EntryNativeAt (V : Type u) (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (Admission : NativeMachine → SourceScope.SourceFiber → Bool → Prop)
    (Post : V → Moves.NIteration → Prop) : Prop :=
  ∀ machine fiber yielding, Admission machine fiber yielding → EntryAt spec fragment machine fiber →
    ∃ world, Post world (evaluateNative spec.root machine fiber yielding spec.table)

/-- Admission reads precisely the native machine and fiber used by the actual entry branch. -/
def EntryRun.Admitted (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (Admission : NativeMachine → SourceScope.SourceFiber → Bool → Prop)
    {machine : NativeMachine} {fiber : SourceScope.SourceFiber} {yielding : Bool} {result : Moves.NIteration}
    (_run : EntryRun spec fragment machine fiber yielding result) : Prop :=
  Admission machine (countOp (runloopTop fiber)) yielding ∧
    Admission
      (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
      {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}} true

/-- The real application entry consumes the same admission and returns the same chosen proof world. -/
theorem EntryRun.attach {V : Type u} (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (Admission : NativeMachine → SourceScope.SourceFiber → Bool → Prop) (Post : V → Moves.NIteration → Prop)
    (enter : EntryNativeAt V spec fragment Admission Post)
    {machine : NativeMachine} {fiber : SourceScope.SourceFiber} {yielding : Bool} {result : Moves.NIteration}
    (run : EntryRun spec fragment machine fiber yielding result) (admitted : EntryRun.Admitted spec fragment Admission run) :
    ∃ world, Post world result := by
  cases run with
  | plain entry actual =>
    rw [actual]
    exact enter _ _ _ admitted.1 entry
  | injected entry actual =>
    rw [actual]
    exact enter _ _ _ admitted.2 entry

/-- The actual pending iteration activates only through its contextual admitted native entry. -/
theorem pending_iteration_attach_contextual {V : Type u} (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (Admission : NativeMachine → SourceScope.SourceFiber → Bool → Prop) (Post : V → Moves.NIteration → Prop)
    (enter : EntryNativeAt V spec fragment Admission Post)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (held : FramesAt spec fragment false machine) (heap : HeapPrefix spec machine.state)
    (admitted : ∀ result (run : EntryRun spec fragment machine fiber yielding result), EntryRun.Admitted spec fragment Admission run) :
    let result := iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding
    (HeapPrefix spec result.machine.state ∧ result.machine.nextId = machine.nextId ∧
      AnswerFlow.IterFlows (fun world _ => FrameAt spec fragment world) (fun state id => ⟨id, state, false⟩) result) ∨
      ∃ world, Post world result := by
  rcases pending_iteration_or_entry spec fragment machine fiber yielding input output owned saved held heap with pending | entry
  · exact .inl pending
  · exact .inr (EntryRun.attach spec fragment Admission Post enter entry (admitted _ entry))
end Effect4.Program.AnswerSlots.AllocationAdapter
