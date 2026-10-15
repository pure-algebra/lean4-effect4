import Effect4.Laws.Program.AnswerSlots.AllocationPending
import Effect4.Laws.Program.PrimitiveProducer
import Effect4.Laws.Machine.StatePreservation
import Effect4.Laws.Program.NativeFrameRows
import Effect4.Laws.Program.Footprint

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: every actual pending initializer primitive retains its exact saved answer graph.
Reach: real native evaluation before the source entry hook, using the shared primitive producer.
Consumer: Atomic's bare-prefix iteration and coupled stage history.
The entry branch must first install the application's checked numeric invariant.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- A real ordinary pending frame step uses the shared head law and actual drained-frame law. -/
theorem pending_step_frame_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (world : World) (input output : Kind spec.stable.Kind)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (owned : CodeAt spec world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment world) input output fiber.frame.stack)
    (noSuccess : ∀ value, fiber.frame.current ≠ .success value)
    (noFailure : ∀ cause, fiber.frame.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.frame.current ≠ .sync thunk) :
    (let next := evaluatePrim.stepFrame (interpAt spec.root view spec.table) machine fiber yielding
    ∃ result, AnswerFlow.FamilyResult (model spec view) (Edge spec fragment) world result
      next.fiber.frame.current next.fiber.frame.stack) ∨
    ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧ Entry spec world point := by
  rcases nonterminal_step_or_entry spec fragment view world input output fiber.frame owned saved noSuccess noFailure noSync with step | entry
  · apply Or.inl
    unfold evaluatePrim.stepFrame
    cases actual : fiber.frame.step (interpAt spec.root view spec.table).toPrimInterp with
    | mk next events =>
      rw [actual] at step
      cases next with
      | running frame => exact ⟨output, step⟩
      | finished exit =>
        exact AnswerFlow.External.Native.finished_frame (model spec view) (interpAt spec.root view spec.table)
          (Edge spec fragment) world input output fiber.frame exit owned (congrArg Prod.fst actual)
  · exact .inr entry

/-- Every actual primitive before source entry follows the exact pending answer graph. -/
theorem pending_primitive_frame_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (heap : HeapPrefix spec machine.state) :
    (let next := evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding
    HeapPrefix spec next.machine.state ∧ FrameAt spec fragment ⟨fiber.id, next.machine.state, false⟩ next.fiber.frame) ∨
    ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧
      Entry spec ⟨fiber.id, machine.state, false⟩ point := by
  rcases pending_ordinary_or_entry spec view ⟨fiber.id, machine.state, false⟩ input fiber.frame.current owned rfl with ordinary | entry
  swap
  · exact .inr entry
  have producer := Moves.evaluatePrim_producer (interpAt spec.root view spec.table) machine fiber yielding
  generalize actual : evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding = result at producer ⊢
  dsimp only
  cases producer with
  | step unparked action noSync noSuccess noFailure noYield noAsync =>
    have state := StatePreservation.stepFrame (interpAt spec.root view spec.table)
      (fun state => state = machine.state) machine fiber yielding rfl
    rw [state]
    rcases pending_step_frame_or_entry spec fragment view _ input output machine fiber yielding owned saved noSuccess noFailure noSync with result | entry
    · obtain ⟨output, input, code, path⟩ := result
      exact .inl ⟨heap, input, output, code, path⟩
    · exact .inr entry
  | finalizer exit current =>
    have state := StatePreservation.finalizerOr (interpAt spec.root view spec.table)
      (fun state => state = machine.state) machine fiber yielding exit rfl
    rw [state]
    rcases finalizer_frame_or_entry spec fragment view _ input output machine fiber yielding exit current owned saved with result | entry
    · obtain ⟨output, input, code, path⟩ := result
      exact .inl ⟨heap, input, output, code, path⟩
    · exact .inr entry
  | sync thunk state value current unparked found =>
    rcases pending_sync_heap_or_entry spec view _ input thunk state value (current ▸ owned) rfl heap found with heapAfter | entry
    swap
    · obtain ⟨point, kind, code, stage⟩ := entry
      exact .inr ⟨point, kind, current.trans code, stage⟩
    rcases sync_frame_or_entry spec fragment view _ input output fiber.frame thunk state value current owned saved found with result | entry
    · obtain ⟨input, code, path⟩ := result
      exact .inl ⟨heapAfter, input, output, code, path⟩
    · exact .inr entry
  | fallback thunk current unparked missing =>
    rcases fallback_or_entry spec view _ input thunk (current ▸ owned) missing with good | entry
    · exact .inl ⟨heap, input, output, .success good, saved⟩
    · obtain ⟨point, kind, code, stage⟩ := entry
      exact .inr ⟨point, kind, current.trans code, stage⟩
  | yieldNow priority current =>
    rcases yield_frame_or_entry spec fragment _ input output fiber.frame priority owned rfl current saved with result | entry
    · obtain ⟨input, code, path⟩ := result
      exact .inl ⟨heap, input, output, code, path⟩
    · exact .inr entry
  | action thunk action current unparked found => exact (ordinary.2.1 thunk current).elim
  | asyncImmediate name signal cancel state code current registered => exact (ordinary.2.2 name signal cancel current).elim
  | asyncParked name signal cancel state current registered => exact (ordinary.2.2 name signal cancel current).elim
  | rejectedPark cause park | racePark race park
    | countdownPark targets next returned parked edits park counted
    | joinMissing target mode park missing | joinExited target mode other exit park found exited
    | joinWaiting target mode other park found live =>
    rw [ordinary.1] at park
    cases park

/-- The actual pending primitive supplies whole installed-row flow or its exact application entry witness. -/
theorem pending_primitive_iterflows_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (held : FramesAt spec fragment false machine) (heap : HeapPrefix spec machine.state) :
    (HeapPrefix spec (evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding).machine.state ∧
    AnswerFlow.IterFlows (fun world _ => FrameAt spec fragment world) (fun state id => ⟨id, state, false⟩)
      (evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding)) ∨
    ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧
      Entry spec ⟨fiber.id, machine.state, false⟩ point := by
  rcases pending_ordinary_or_entry spec view ⟨fiber.id, machine.state, false⟩ input fiber.frame.current owned rfl with ordinary | entry
  swap
  · exact .inr entry
  rcases pending_primitive_frame_or_entry spec fragment view machine fiber yielding input output owned saved heap with result | entry
  swap
  · exact .inr entry
  obtain ⟨heapAfter, code⟩ := result
  apply Or.inl
  refine ⟨heapAfter, ?_⟩
  let next := evaluatePrim (interpAt spec.root view spec.table) machine fiber yielding
  have key := (Moves.evaluatePrim_footprint (interpAt spec.root view spec.table) machine fiber yielding).id
  have parent : FrameAt spec fragment ⟨next.fiber.id, next.machine.state, false⟩ next.fiber.frame := by
    rw [key]
    exact code
  have actor := FrameAt.pending_owner spec fragment _ fiber.frame ⟨input, output, owned, saved⟩ rfl
  have owners : ∀ row ∈ next.machine.fibers, row.id = fiber.id := by
    apply NativeFrameRows.primitive_rows (interpAt spec.root view spec.table) machine fiber yielding next
      (Moves.evaluatePrim_producer _ _ _ _) (fun id _ => id = fiber.id)
    · intro row member
      exact (FrameAt.pending_owner spec fragment _ row.frame (held row member) rfl).trans actor.symm
    · intro thunk action current unparked found row member
      exact (ordinary.2.1 thunk current).elim
  refine ⟨?_, parent⟩
  intro row member
  obtain ⟨before, present, same⟩ := List.mem_map.mp member
  have chosen : before.id = next.fiber.id := (owners before present).trans key.symm
  rw [← same]
  change FrameAt spec fragment ⟨(if before.id = next.fiber.id then next.fiber else before).id, next.machine.state, false⟩
    (if before.id = next.fiber.id then next.fiber else before).frame
  rw [if_pos chosen]
  exact parent

end Effect4.Program.AnswerSlots.AllocationAdapter
