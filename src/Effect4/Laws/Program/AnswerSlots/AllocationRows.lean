import Effect4.Laws.Program.AnswerSlots.AllocationFrame
import Effect4.Laws.Machine.AnswerFlowRun

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the exact root initializer is exclusive before the actual entry callback.
Reach: current code and actual ordered saved paths, with one shared independent entry flag.
Consumer: old-row transport in the common bare primitive and command producer.
This exclusivity fact does not assert history or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- An actual stored frame retains its input, output and ordered saved suffix. -/
def FrameAt (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  ∃ input output, CodeAt spec world input frame.current ∧
    Effect4.Contracts.Path (Edge spec fragment world) input output frame.stack

/-- Every stored row reads the same independent entry flag and the actual shared native stores. -/
def FramesAt (spec : Spec) (fragment : SourceScope.Fragment spec.root) (entered : Bool) (machine : NativeMachine) : Prop :=
  AnswerFlow.Flows (fun world _ => FrameAt spec fragment world) (fun state id => ⟨id, state, entered⟩) machine

/-- Before actual entry, the only admitted frame owner is the real root identity. -/
theorem FrameAt.pending_owner (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (held : FrameAt spec fragment world frame)
    (pending : world.entered = false) : world.owner = ⟨0⟩ := by
  obtain ⟨input, output, code, saved⟩ := held
  rcases code_phase spec world input frame.current code with owner | ready
  · exact owner
  · exact (pending_not_ready spec world pending ready).elim

/-- A ready frame retains its code and saved suffix through arbitrary permitted native growth. -/
theorem FrameAt.future_ready (spec : Spec) (fragment : SourceScope.Fragment spec.root) (first last : World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (held : FrameAt spec fragment first frame)
    (future : Future first last) (ready : Ready spec first) : FrameAt spec fragment last frame := by
  obtain ⟨input, output, code, saved⟩ := held
  exact ⟨input, output, code_future_ready spec first input frame.current code last future ready,
    path_future spec fragment first last future input output frame.stack saved⟩

/-- Every distinct nonacting row is already stable; pending allocation has only the root owner. -/
theorem FrameAt.other (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (state next : Stores) (entered : Bool) (actor owner : FiberId)
    (first last : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (acting : FrameAt spec fragment ⟨actor, state, entered⟩ first)
    (held : FrameAt spec fragment ⟨owner, state, entered⟩ last) (different : actor ≠ owner)
    (growth : state.refs.length ≤ next.refs.length ∧ state.deferreds.cells.length ≤ next.deferreds.cells.length) :
    FrameAt spec fragment ⟨owner, next, entered⟩ last := by
  cases pending : entered with
  | false =>
    have one := FrameAt.pending_owner spec fragment _ first acting pending
    have two := FrameAt.pending_owner spec fragment _ last held pending
    exact (different (one.trans two.symm)).elim
  | true =>
    obtain ⟨input, output, code, saved⟩ := held
    have ready : Ready spec ⟨owner, state, entered⟩ := by
      rcases code_phase spec _ input last.current code with root | ready
      · obtain ⟨actorInput, actorOutput, actorCode, actorSaved⟩ := acting
        rcases code_phase spec _ actorInput first.current actorCode with actorRoot | actorReady
        · exact (different (actorRoot.trans root.symm)).elim
        · exact actorReady
      · exact ready
    exact FrameAt.future_ready spec fragment _ _ last ⟨input, output, code, saved⟩
      ⟨rfl, growth.1, growth.2, fun _ => rfl⟩ ready

end Effect4.Program.AnswerSlots.AllocationAdapter
