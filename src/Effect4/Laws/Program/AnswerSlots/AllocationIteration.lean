import Effect4.Laws.Program.AnswerSlots.AllocationCounter
import Effect4.Laws.Program.AnswerSlots.AllocationEntrySuffix

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Question: the real charged iteration enters the numeric application at its actual source point.
Reach: pending interruption, scheduler injection, native evaluation and the retained older suffix.
Consumer: Atomic's coupled initializer and request-stage command producer.
These local transitions do not assert scheduler progress or a completed history.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- A native input reaches the actual post-prefix source point with its older saved suffix. -/
def EntryAt (spec : Spec) (fragment : SourceScope.Fragment spec.root) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) : Prop :=
  ∃ point output, fiber.frame.current = resolve spec.root point ∧
    Entry spec ⟨fiber.id, machine.state, false⟩ point ∧
    Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩)
      (.stable spec.stable.rootKind) output fiber.frame.stack

/-- The real older suffix at source entry transfers as identity masks into the application model. -/
theorem EntryAt.mask_suffix (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (entry : EntryAt spec fragment machine fiber) :
    MaskSuffix fiber.frame.stack := by
  obtain ⟨point, output, current, stage, saved⟩ := entry
  exact (pending_root_path spec fragment ⟨fiber.id, machine.state, false⟩ rfl fiber.frame.stack output saved).2

/-- The actual iteration reaches entry either directly or through its real scheduler injection. -/
inductive EntryRun (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (result : Moves.NIteration) : Prop where
  | plain (entry : EntryAt spec fragment machine (countOp (runloopTop fiber)))
      (actual : result = evaluateNative spec.root machine (countOp (runloopTop fiber)) yielding spec.table) :
      EntryRun spec fragment machine fiber yielding result
  | injected
      (entry : EntryAt spec fragment
        (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}})
      (actual : result = evaluateNative spec.root
        (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}} true spec.table) :
      EntryRun spec fragment machine fiber yielding result

/-- The loop top retains its actual answer endpoints when a pending interrupt installs failure. -/
theorem loop_top (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (input output : Kind spec.stable.Kind) (fiber : SourceScope.SourceFiber)
    (owned : CodeAt spec world input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment world) input output fiber.frame.stack) :
    AnswerFlow.FamilyResult (model spec []) (Edge spec fragment) world output
      (countOp (runloopTop fiber)).frame.current (countOp (runloopTop fiber)).frame.stack := by
  unfold countOp runloopTop
  split
  · exact ⟨input, .failure (code_phase spec world input _ owned), saved⟩
  · exact ⟨input, owned, saved⟩

/-- The actual charged iteration either retains pending flow or supplies its exact application entry. -/
theorem pending_iteration_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (held : FramesAt spec fragment false machine) (heap : HeapPrefix spec machine.state) :
    let result := iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding
    (HeapPrefix spec result.machine.state ∧ result.machine.nextId = machine.nextId ∧
      AnswerFlow.IterFlows (fun world _ => FrameAt spec fragment world) (fun state id => ⟨id, state, false⟩) result) ∨
      EntryRun spec fragment machine fiber yielding result := by
  have topId : (countOp (runloopTop fiber)).id = fiber.id := by
    unfold countOp runloopTop
    split <;> rfl
  obtain ⟨topKind, code, stack⟩ := loop_top spec fragment ⟨fiber.id, machine.state, false⟩ input output fiber owned saved
  generalize actual : iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding = result
  dsimp only
  unfold iteration at actual
  dsimp only at actual
  split at actual
  · rename_i injectedResult injected
    cases actual
    unfold injectYield at injected
    split at injected
    · cases injected
      have typed : CodeAt spec ⟨fiber.id, machine.state, false⟩ topKind
          (.onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current) :=
        .yieldThen (code_phase spec _ topKind _ code) code (fun _ => ⟨rfl, heap.1⟩)
      rcases pending_native_counted_iterflows_or_entry spec fragment
        (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}}
        true topKind output (by rw [topId]; exact typed) (by rw [topId]; exact stack) held heap with flow | entry
      · exact .inl flow
      · obtain ⟨point, kind, current, stage⟩ := entry
        subst topKind
        exact .inr (.injected ⟨point, output, current, stage, by rw [topId]; exact stack⟩ rfl)
    · cases injected
  · cases actual
    rcases pending_native_counted_iterflows_or_entry spec fragment machine (countOp (runloopTop fiber)) yielding
      topKind output (by rw [topId]; exact code) (by rw [topId]; exact stack) held heap with flow | entry
    · exact .inl flow
    · obtain ⟨point, kind, current, stage⟩ := entry
      subst topKind
      exact .inr (.plain ⟨point, output, current, stage, by rw [topId]; exact stack⟩ rfl)

end Effect4.Program.AnswerSlots.AllocationAdapter
