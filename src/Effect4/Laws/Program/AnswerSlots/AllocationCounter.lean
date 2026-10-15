import Effect4.Laws.Program.AnswerSlots.AllocationScoped
import Effect4.Laws.Program.PrimitiveCounter

/-!
Concept: store-typing R4, serving `Atomic.Store.shop_stages`.
Consumer: the exact common initializer iteration and its actual root role activation.
Pending source execution retains the fiber-allocation counter or exposes its actual entry point.
All counter facts read the existing evaluator and primitive producer.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Actual pending native dispatch is the existing primitive dispatcher or the exact application entry. -/
theorem pending_native_primitive_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack) :
    evaluateNative spec.root machine fiber yielding spec.table =
      evaluatePrim (interpAt spec.root machine.completedExits spec.table) machine fiber yielding ∨
      ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧
        Entry spec ⟨fiber.id, machine.state, false⟩ point := by
  rcases pending_ordinary_or_entry spec machine.completedExits ⟨fiber.id, machine.state, false⟩ input fiber.frame.current owned rfl with ordinary | entry
  swap
  · exact .inr entry
  unfold evaluateNative
  split
  · rename_i point current
    exact (ordinary.2.1 (.act point) current).elim
  · rename_i value current
    exact pending_exit_eq_or_entry spec fragment machine fiber yielding input output (.success value) current owned saved
  · rename_i cause current
    exact pending_exit_eq_or_entry spec fragment machine fiber yielding input output (.failure cause) current owned saved
  · exact .inl rfl

/-- The actual pending native evaluator cannot allocate a fiber before application entry. -/
theorem pending_native_counter_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack) :
    (evaluateNative spec.root machine fiber yielding spec.table).machine.nextId = machine.nextId ∨
      ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧
        Entry spec ⟨fiber.id, machine.state, false⟩ point := by
  rcases pending_ordinary_or_entry spec machine.completedExits ⟨fiber.id, machine.state, false⟩ input fiber.frame.current owned rfl with ordinary | entry
  swap
  · exact .inr entry
  rcases pending_native_primitive_or_entry spec fragment machine fiber yielding input output owned saved with same | entry
  · exact .inl ((congrArg (fun result : Moves.NIteration => result.machine.nextId) same).trans
      (Moves.evaluatePrim_nextId (interpAt spec.root machine.completedExits spec.table) machine fiber yielding ordinary.1 ordinary.2.1))
  · exact .inr entry

/-- Exact heap, fiber counter and row flow refer to one actual native result. -/
theorem pending_native_counted_iterflows_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (held : FramesAt spec fragment false machine) (heap : HeapPrefix spec machine.state) :
    (HeapPrefix spec (evaluateNative spec.root machine fiber yielding spec.table).machine.state ∧
      (evaluateNative spec.root machine fiber yielding spec.table).machine.nextId = machine.nextId ∧
      AnswerFlow.IterFlows (fun world _ => FrameAt spec fragment world) (fun state id => ⟨id, state, false⟩)
        (evaluateNative spec.root machine fiber yielding spec.table)) ∨
      ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧
        Entry spec ⟨fiber.id, machine.state, false⟩ point := by
  rcases pending_native_counter_or_entry spec fragment machine fiber yielding input output owned saved with counter | entry
  · rcases pending_native_iterflows_or_entry spec fragment machine fiber yielding input output owned saved held heap with result | entry
    · exact .inl ⟨result.1, counter, result.2⟩
    · exact .inr entry
  · exact .inr entry
end Effect4.Program.AnswerSlots.AllocationAdapter
