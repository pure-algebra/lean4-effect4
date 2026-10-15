import Effect4.Laws.Program.AnswerSlots.AllocationIteration

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: Atomic and Queue actual initialization-to-application native producers.
The existing allocation iteration supplies the actual pending result or exact source entry.
The application evaluates that same entry and retains one chosen proof world for its whole postcondition.
No command preservation or history assertion follows without its local producers.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program
universe u

/-- The application native contract reads the real entry frame, heap and saved mask suffix. -/
def EntryNative (V : Type u) (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (Post : V → Moves.NIteration → Prop) : Prop :=
  ∀ machine fiber yielding, EntryAt spec fragment machine fiber →
    ∃ world, Post world (evaluateNative spec.root machine fiber yielding spec.table)

/-- One actual pending iteration either retains the allocation invariant or activates the application.
`Post` can retain flow, machine, command queue and snapshot facts at the same chosen world. -/
theorem pending_iteration_attach {V : Type u} (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (Post : V → Moves.NIteration → Prop) (enter : EntryNative V spec fragment Post)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (held : FramesAt spec fragment false machine) (heap : HeapPrefix spec machine.state) :
    let result := iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding
    (HeapPrefix spec result.machine.state ∧ result.machine.nextId = machine.nextId ∧
      AnswerFlow.IterFlows (fun world _ => FrameAt spec fragment world) (fun state id => ⟨id, state, false⟩) result) ∨
      ∃ world, Post world result := by
  rcases pending_iteration_or_entry spec fragment machine fiber yielding input output owned saved held heap with pending | entry
  · exact .inl pending
  · apply Or.inr
    cases entry with
    | plain actual same =>
      rw [same]
      exact enter _ _ _ actual
    | injected actual same =>
      rw [same]
      exact enter _ _ _ actual
/-- One returned world distinguishes actual pending allocation from active application execution. -/
def NativePost {V : Type u} (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (Post : V → Moves.NIteration → Prop) (before : NativeMachine)
    (world : Option V) (result : Moves.NIteration) : Prop :=
  match world with
  | none => HeapPrefix spec result.machine.state ∧ result.machine.nextId = before.nextId ∧
      AnswerFlow.IterFlows (fun current _ => FrameAt spec fragment current)
        (fun state id => ⟨id, state, false⟩) result
  | some active => Post active result

/-- The existing pending iteration chooses one world for all of its actual native postcondition. -/
theorem pending_iteration_world {V : Type u} (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (Post : V → Moves.NIteration → Prop) (enter : EntryNative V spec fragment Post)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (held : FramesAt spec fragment false machine) (heap : HeapPrefix spec machine.state) :
    ∃ world, NativePost spec fragment Post machine world
      (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding) := by
  rcases pending_iteration_attach spec fragment Post enter machine fiber yielding input output owned saved held heap with pending | active
  · exact ⟨none, pending⟩
  · obtain ⟨world, post⟩ := active
    exact ⟨some world, post⟩
end Effect4.Program.AnswerSlots.AllocationAdapter
