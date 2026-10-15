import Effect4.Laws.Program.AnswerSlots.InitializedGrowth
import Effect4.Laws.Program.AnswerSlots.InitializedOtherRows
import Effect4.Laws.Program.NativeActionRows

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: initialized native operations retain all stored frames, including actual action births.
Reach: actual frame owners, uniform saved paths, allocation growth and the existing action-row producer.
Limit: the acting parent's returned frame and command settlement use their separate local producers.
Consumer: the joint crew command flow and release-log histories.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Stored log safety keeps an actual input and an existential output, including exited frames. -/
def FrameAt (spec : Spec) (world : World) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  ∃ input output, CodeAt spec world input frame.current ∧
    Effect4.Contracts.Path (Edge spec [] world) input output frame.stack

/-- Every stored fiber reads the initialized graph at its actual identity and shared store. -/
def FramesAt (spec : Spec) (machine : NativeMachine) : Prop :=
  AnswerFlow.Flows (fun world _ => FrameAt spec world) (fun state id => ⟨id, state⟩) machine

/-- Current code and saved stack are the only frame fields this invariant reads. -/
theorem FrameAt.fields {spec : Spec} {world : World}
    {first last : FrameFiber EffName EffThunk Val Err Defect FiberId Ann}
    (held : FrameAt spec world first) (current : last.current = first.current) (stack : last.stack = first.stack) :
    FrameAt spec world last := by
  rw [FrameAt, current, stack]
  exact held

/-- Clearing an exited frame may choose its current input as its new existential output. -/
theorem FrameAt.cleared (spec : Spec) (world : World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (held : FrameAt spec world frame) :
    FrameAt spec world {frame with stack := []} := by
  obtain ⟨input, output, code, saved⟩ := held
  exact ⟨input, input, code, .nil input⟩

/-- A delivered failure retains the old input and its actual saved suffix. -/
theorem FrameAt.failure (spec : Spec) (world : World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (held : FrameAt spec world frame) : FrameAt spec world {frame with current := .failure cause} := by
  obtain ⟨input, output, code, saved⟩ := held
  exact ⟨input, output, .failure (code_phase spec world input frame.current code), saved⟩

/-- Native interrupt recording changes metadata or installs its actual failure. -/
theorem FrameAt.interruption (spec : Spec) (world : World) (fiber : SourceScope.SourceFiber) (cause : CauseV)
    (held : FrameAt spec world fiber.frame) : FrameAt spec world (interruptWithCause cause fiber).1.frame := by
  obtain ⟨input, output, code, saved⟩ := held
  have phase := code_phase spec world input fiber.frame.current code
  unfold interruptWithCause
  dsimp only
  repeat' split
  all_goals refine ⟨input, output, ?_, saved⟩
  all_goals aesop (add norm simp [frameCore]) (add safe apply [CodeAt.failure])

/-- Equal allocation counts transport every old frame through native administration. -/
theorem FrameAt.rebase (spec : Spec) (first last : World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (held : FrameAt spec first frame)
    (future : Future first last) (refs : first.state.refs.length = last.state.refs.length)
    (deferred : first.state.deferreds.cells.length = last.state.deferreds.cells.length) : FrameAt spec last frame := by
  obtain ⟨input, output, code, saved⟩ := held
  exact ⟨input, output, code_rebase spec first input frame.current code last future refs deferred,
    path_future spec [] first last future input output frame.stack saved⟩

/-- A distinct nonacting owner is already ready, so actual growing stores retain its frame. -/
theorem FrameAt.other (spec : Spec) (state next : Stores) (actor owner : FiberId)
    (first last : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (acting : FrameAt spec ⟨actor, state⟩ first) (held : FrameAt spec ⟨owner, state⟩ last)
    (different : actor ≠ owner) (growth : Bounds state.refs.length state.deferreds.cells.length next) :
    FrameAt spec ⟨owner, next⟩ last := by
  obtain ⟨actorKind, actorOutput, code, stack⟩ := acting
  obtain ⟨input, output, owned, saved⟩ := held
  exact ⟨input, output, other_code spec state next actor owner actorKind input first.current last.current
    code owned different growth.1 growth.2,
    path_future spec [] ⟨owner, state⟩ ⟨owner, next⟩ ⟨rfl, growth.1, growth.2⟩ input output last.stack saved⟩

/-- Actual action births start at their certified broad source class; old rows retain exact counts. -/
theorem action_rows (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (input : Kind) (thunk : EffThunk) (action : NAction)
    (current : fiber.frame.current = .withFiber thunk)
    (owned : CodeAt spec ⟨fiber.id, machine.state⟩ input fiber.frame.current)
    (found : (interpAt spec.root view spec.table).withFiberOf thunk = some action)
    (held : FramesAt spec machine) :
    FramesAt spec (evaluatePrim.withFiber (interpAt spec.root view spec.table) machine fiber yielding action).machine := by
  obtain ⟨same, ready, permission⟩ := action_shape spec _ input thunk (current ▸ owned)
  let next := evaluatePrim.withFiber (interpAt spec.root view spec.table) machine fiber yielding action
  have counts := action_counts spec view machine fiber yielding action
  have programs := Typed.interp_action_at spec.toSpec fragment view thunk action permission found
  apply SourceScope.with_fiber_frame_rows spec.root view spec.table (Typed.CodeAt spec.toSpec .root)
    (fun id frame => FrameAt spec ⟨id, next.machine.state⟩ frame) machine fiber yielding action
  · intro row member
    exact FrameAt.rebase spec ⟨row.id, machine.state⟩ ⟨row.id, next.machine.state⟩ row.frame (held row member)
      ⟨rfl, Nat.le_of_eq counts.1.symm, Nat.le_of_eq counts.2.symm⟩ counts.1.symm counts.2.symm
  · exact programs
  · intro id frame code empty
    refine ⟨.stable .root, .stable .root, .stable ?_ code, ?_⟩
    · exact ready_future spec ⟨fiber.id, machine.state⟩ ⟨fiber.id, next.machine.state⟩
        ⟨rfl, Nat.le_of_eq counts.1.symm, Nat.le_of_eq counts.2.symm⟩ ready
    · rw [empty]
      exact .nil _
end Effect4.Program.AnswerSlots.Initialized
