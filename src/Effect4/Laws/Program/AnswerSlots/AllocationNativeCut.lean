import Effect4.Laws.Program.AnswerSlots.AllocationConfiguration
import Effect4.Laws.Program.PrimitiveEffects

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the common pending allocation settlement and contextual application attachment.
One actual native cut retains exact heap, counter, parked reply suffix, stored frames and addressed effects together.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- All local pending facts describe the same actual native result. -/
structure PendingNativeCut (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (result : Moves.NIteration) : Prop where
  heap : HeapPrefix spec result.machine.state
  counter : result.machine.nextId = machine.nextId
  flows : AnswerFlow.IterFlows (fun world _ => PendingFrame spec fragment world)
    (fun state id => ⟨id, state, false⟩) result
  waits : PendingWaits spec fragment ⟨result.fiber.id, result.machine.state, false⟩ result.fiber
  footprint : Moves.Footprint fiber result.fiber
  effects : Moves.QuietEffects result
  dispatcher : result.machine.fibers = machine.fibers ∧
    (Replies fiber.dispatcher → Replies result.fiber.dispatcher)
  recorded : result.fiber.frame.interruptedCause = fiber.frame.interruptedCause
  deferred : DeferredQuiet machine.state.deferreds → DeferredQuiet result.machine.state.deferreds

/-- Actual pending native evaluation returns one joint pending cut or its exact application entry. -/
theorem pending_native_cut_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (held : FramesAt spec fragment false machine) (heap : HeapPrefix spec machine.state)
    (unparked : fiber.parked = .notParked) :
    PendingNativeCut spec fragment machine fiber (evaluateNative spec.root machine fiber yielding spec.table) ∨
      ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧
        Entry spec ⟨fiber.id, machine.state, false⟩ point := by
  rcases pending_native_counted_iterflows_or_entry spec fragment machine fiber yielding input output owned saved held heap with flow | entry
  swap
  · exact .inr entry
  rcases pending_native_waits_or_entry spec fragment machine fiber yielding input output owned saved unparked with waits | entry
  swap
  · exact .inr entry
  rcases pending_metadata_or_entry spec machine.completedExits ⟨fiber.id, machine.state, false⟩ input fiber.frame.current owned rfl with ordinary | entry
  swap
  · exact .inr entry
  rcases pending_native_primitive_or_entry spec fragment machine fiber yielding input output owned saved with same | entry
  swap
  · exact .inr entry
  have footprint := Moves.evaluateNative_footprint spec.root spec.table machine fiber yielding
  refine .inl ⟨flow.1, flow.2.1, ?_, ?_, footprint, ?_, ?_,
    Guard.Interruption.evaluateNative_interruptedCause spec.root spec.table machine fiber yielding, ?_⟩
  · exact ⟨fun row member => ⟨flow.2.2.1 row member, flow.1⟩, ⟨flow.2.2.2, flow.1⟩⟩
  · rw [footprint.id]
    exact waits
  · rw [same]
    exact Moves.evaluatePrim_quiet (interpAt spec.root machine.completedExits spec.table) machine fiber yielding ordinary.1 ordinary.2.1
  · rw [same]
    constructor
    · have arbitrary : DispatcherPredicate.All (fun (_ : SourceScope.SourceTask) => True) fiber.dispatcher :=
        fun _ _ _ _ => trivial
      exact (Moves.evaluatePrim_dispatcher (interpAt spec.root machine.completedExits spec.table) machine fiber yielding
        (fun _ => True) (fun _ _ => trivial) arbitrary ordinary.1 ordinary.2.1).1
    · intro replies
      exact (Moves.evaluatePrim_dispatcher (interpAt spec.root machine.completedExits spec.table) machine fiber yielding
        ReplyTask (fun owner token => reply_success owner token _) replies ordinary.1 ordinary.2.1).2

  · intro quiet
    rw [same]
    apply StatePreservation.primitive_at (interpAt spec.root machine.completedExits spec.table)
      (fun state => DeferredQuiet state.deferreds) machine fiber yielding quiet
    · intro thunk state value current ran
      exact ordinary.2.2.2 thunk state value current ran quiet
    · intro name signal cancel current
      exact (ordinary.2.2.1 name signal cancel current).elim
    · intro thunk action current found
      exact (ordinary.2.1 thunk current).elim

/-- The common iteration walk retains the joint pending cut through charging and yield injection. -/
theorem pending_iteration_cut_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (held : FramesAt spec fragment false machine) (heap : HeapPrefix spec machine.state)
    (unparked : fiber.parked = .notParked) :
    let result := iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding
    PendingNativeCut spec fragment machine fiber result ∨ EntryRun spec fragment machine fiber yielding result := by
  let Post := fun result : Moves.NIteration =>
    HeapPrefix spec result.machine.state ∧ result.machine.nextId = machine.nextId ∧
    AnswerFlow.IterFlows (fun world _ => PendingFrame spec fragment world)
      (fun state id => ⟨id, state, false⟩) result ∧
    PendingWaits spec fragment ⟨result.fiber.id, result.machine.state, false⟩ result.fiber ∧
    Moves.QuietEffects result ∧ result.machine.fibers = machine.fibers ∧
      (Replies fiber.dispatcher → Replies result.fiber.dispatcher) ∧
    (DeferredQuiet machine.state.deferreds → DeferredQuiet result.machine.state.deferreds)
  have admitted : (countOp (runloopTop fiber)).parked = .notParked := by
    unfold countOp runloopTop
    split <;> exact unparked
  have localNative : ∀ actual actor y first last,
      (actual.nextId = machine.nextId ∧ actor.parked = .notParked ∧ actual.fibers = machine.fibers ∧ actor.dispatcher = fiber.dispatcher ∧
        actual.state.deferreds = machine.state.deferreds) →
      CodeAt spec ⟨actor.id, actual.state, false⟩ first actor.frame.current →
      Effect4.Contracts.Path (Edge spec fragment ⟨actor.id, actual.state, false⟩) first last actor.frame.stack →
      FramesAt spec fragment false actual → HeapPrefix spec actual.state →
      Post (evaluateNative spec.root actual actor y spec.table) ∨
        ∃ point, first = .stable spec.stable.rootKind ∧ actor.frame.current = resolve spec.root point ∧
          Entry spec ⟨actor.id, actual.state, false⟩ point := by
    intro actual actor y first last permission current suffix frames contents
    rcases pending_native_cut_or_entry spec fragment actual actor y first last current suffix frames contents permission.2.1 with cut | entry
    · exact .inl ⟨cut.heap, cut.counter.trans permission.1, cut.flows, cut.waits, cut.effects,
        cut.dispatcher.1.trans permission.2.2.1,
        fun replies => cut.dispatcher.2 (permission.2.2.2.1.symm ▸ replies),
        fun quiet => cut.deferred (permission.2.2.2.2.symm ▸ quiet)⟩
    · exact .inr entry
  rcases pending_iteration_of_native spec fragment Post
    (fun actual actor _ => actual.nextId = machine.nextId ∧ actor.parked = .notParked ∧ actual.fibers = machine.fibers ∧ actor.dispatcher = fiber.dispatcher ∧
        actual.state.deferreds = machine.state.deferreds)
    localNative machine fiber yielding input output owned saved held heap
    (by
      have dispatcher : (countOp (runloopTop fiber)).dispatcher = fiber.dispatcher := by
        unfold countOp runloopTop
        split <;> rfl
      exact ⟨⟨rfl, admitted, rfl, dispatcher, rfl⟩, ⟨rfl, admitted, rfl, dispatcher, rfl⟩⟩) with result | entry
  · obtain ⟨heap, counter, flows, waits, effects, rows, replies, quiet⟩ := result
    exact .inl ⟨heap, counter, flows, waits,
      Moves.iteration_footprint spec.root spec.table (interpOf spec.root spec.table) machine fiber yielding,
      effects, ⟨rows, replies⟩,
      Guard.Interruption.iteration_interruptedCause spec.root spec.table machine fiber yielding, quiet⟩
  · exact .inr entry

/-- Before entry every updated stored row is the actual returned root fiber. -/
theorem PendingNativeCut.rows (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (result : Moves.NIteration)
    (cut : PendingNativeCut spec fragment machine fiber result)
    (row : SourceScope.SourceFiber) (member : row ∈ (result.machine.update result.fiber).fibers) : row = result.fiber := by
  obtain ⟨old, present, same⟩ := List.mem_map.mp member
  have root : result.fiber.id = ⟨0⟩ := FrameAt.pending_owner spec fragment _ result.fiber.frame cut.flows.2.1 rfl
  rw [← same]
  change (if old.id = result.fiber.id then result.fiber else old) = result.fiber
  split
  · rfl
  · rename_i different
    have held := cut.flows.1 row member
    rw [← same] at held
    change PendingFrame spec fragment ⟨(if old.id = result.fiber.id then result.fiber else old).id, result.machine.state, false⟩
      (if old.id = result.fiber.id then result.fiber else old).frame at held
    rw [if_neg different] at held
    have oldRoot := FrameAt.pending_owner spec fragment _ old.frame held.1 rfl
    exact (different (oldRoot.trans root.symm)).elim

/-- The joint native cut preserves the entire pending machine configuration after the actual actor update. -/
theorem PendingNativeCut.configuration (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (result : Moves.NIteration)
    (before : PendingConfiguration spec fragment machine) (member : fiber ∈ machine.fibers)
    (cut : PendingNativeCut spec fragment machine fiber result) :
    PendingConfiguration spec fragment (result.machine.update result.fiber) := by
  refine ⟨cut.heap, ?_, ?_, ?_, ?_, cut.counter.trans before.counter, ?_, ?_, cut.deferred before.deferred⟩
  · intro row present
    exact (cut.flows.1 row present).1
  · intro row present
    rw [PendingNativeCut.rows spec fragment machine fiber result cut row present]
    exact cut.waits
  · intro row present
    rw [PendingNativeCut.rows spec fragment machine fiber result cut row present, cut.footprint.children]
    exact before.childless fiber member
  · intro row present
    rw [PendingNativeCut.rows spec fragment machine fiber result cut row present, cut.footprint.observers]
    exact before.unobserved fiber member
  · intro row present
    rw [PendingNativeCut.rows spec fragment machine fiber result cut row present]
    exact cut.dispatcher.2 (before.replies fiber member)
  · intro row present cause recorded
    rw [PendingNativeCut.rows spec fragment machine fiber result cut row present, cut.recorded] at recorded
    exact before.recorded fiber member cause recorded

end Effect4.Program.AnswerSlots.AllocationAdapter
