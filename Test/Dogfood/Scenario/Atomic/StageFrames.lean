import Test.Dogfood.Scenario.Atomic.StageNative

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the joint Atomic native iteration and whole-fiber history invariant.
Every actual saved edge keeps the request owner at both answer endpoints.
The shared saved-family proof handles callbacks and stack pops.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Both answer endpoints of a request saved frame retain that request's owner. -/
theorem edge_owned (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (input output : StageWorld.Kind) (frame : NCode) (held : Edge root table owner world input output frame) :
    Owns owner input ∧ Owns owner output := by
  cases held with
  | saved held => exact ⟨held.inputOwned, held.outputOwned⟩
  | mapped ready held => cases held <;> exact ⟨rfl, rfl⟩

/-- An ordered saved suffix cannot hide a different request's intermediate answer class. -/
theorem path_input_owned (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (input output : StageWorld.Kind) (frames : List NCode)
    (held : Effect4.Contracts.Path (Edge root table owner world) input output frames)
    (owned : Owns owner output) : Owns owner input := by
  cases held with
  | nil => exact owned
  | cons head tail => exact (edge_owned root table owner world _ _ _ head).1

/-- Saved request frames keep their actual captured exits and future-view callback contracts. -/
theorem edge_future (root : NativeEff) (table : RowTable) (owner : Nat)
    (before after : StageWorld.World) (future : Future before after)
    (input output : StageWorld.Kind) (frame : NCode) (held : Edge root table owner before input output frame) :
    Edge root table owner after input output frame := by
  cases held with
  | saved held => exact .saved ⟨ViewSavedAt.future (model root table owner) (fun view => (interpAt root view table).toPrimInterp) (fun _ => future) held.held, held.inputOwned, held.outputOwned⟩
  | mapped ready held => exact .mapped trivial (StageFinalizer.edge_future before after future owner _ _ _ held)

/-- A request frame retains its actual current code and actual ordered older suffix. -/
def FrameAt (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  ∃ input, CodeAt root table owner world input frame.current ∧
    Effect4.Contracts.Path (Edge root table owner world) input (.finalized owner) frame.stack

/-- A different request's actual write retypes this whole frame at the same new world. -/
theorem frame_other (root : NativeEff) (table : RowTable) (owner acting : Nat)
    (before after : StageWorld.World) (future : Future before after) (change : RequestChange before after acting)
    (different : owner ≠ acting) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (held : FrameAt root table owner before frame) : FrameAt root table owner after frame := by
  obtain ⟨input, code, saved⟩ := held
  obtain ⟨stage, cleaned⟩ := change.2 owner different
  exact ⟨input, code_other root table owner before input _ code after future stage cleaned
    (path_input_owned root table owner before input _ _ saved rfl),
    saved.map (edge_future root table owner before after future)⟩

/-- An actual request sync answer retains the whole saved suffix at its chosen heap world. -/
theorem sync_frame (root : NativeEff) (table : RowTable) (owner : Nat) (member : owner ∈ requests)
    (world : StageWorld.World) (state : Stores) (heap : HeapAt world state)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (operation : SyncOp)
    (held : FrameAt root table owner world frame) (current : frame.current = .sync (.op operation)) :
    ∃ next after answer, syncOpStep operation state = some (after, answer) ∧
      Future world next ∧ RequestChange world next owner ∧ HeapAt next after ∧
      FrameAt root table owner next {frame with current := .success answer} := by
  obtain ⟨input, code, saved⟩ := held
  obtain ⟨next, after, answer, actual, future, change, heapNext, good⟩ :=
    sync_heap root table owner member world input operation (current ▸ code) state heap
  exact ⟨next, after, answer, actual, future, change, heapNext, input, .success good,
    saved.map (edge_future root table owner world next future)⟩
end Test.Dogfood.Scenario.Atomic.StageGraph
