import Effect4.Api
import Effect4.Laws.Program.Guard.Interruption

/-!
Probe B1 (research, not a landing): one evaluation edits the evaluated fiber's frame part by a
word of moves. If `evaluatePrim_moves` compiles, the per-field chains of the guard bundle are
instances: a field each move keeps is kept by every evaluation.

The proof style here is the probe's, not a landing's: it uses the unfold list and the case split of
`Guard/Interruption.lean`'s chains.
-/

set_option autoImplicit false

namespace Probe.FrameMoves

open Effect4 Effect4.Machine Effect4.Program

abbrev NFrame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
abbrev NFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev NPrim := PrimInterp EffName EffThunk Val Err Defect FiberId Ann

/-- The moves of one evaluation on the evaluated fiber's frame part. -/
inductive FrameMove : NFrame → NFrame → Prop
  | answer (f : NFrame) (c : NCode) : FrameMove f { f with current := c }
  | push (f : NFrame) (p : NCode) : FrameMove f { f with stack := p :: f.stack }
  | step (interp : NPrim) (f g : NFrame)
      (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) :
      f.step interp = (FrameStep.running g, events) → FrameMove f g
  | finish (interp : NPrim) (f : NFrame) (exit : ExitV)
      (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) :
      f.step interp = (FrameStep.finished exit, events) → FrameMove f (frameExitState f)
  | pop (f : NFrame) (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
      FrameMove f (f.getCont demand skip cause).fiber
  | mask (f : NFrame) : FrameMove f f.uninterruptible
  | unmask (f : NFrame) : FrameMove f f.interruptibleRegion.1
  | pendingFailure (f : NFrame) :
      FrameMove f { f with deferredInterrupt := false, current := Prim.failure f.pendingCause }

/-- Words of moves, built at the end. -/
inductive Moves : NFrame → NFrame → Prop
  | refl (f : NFrame) : Moves f f
  | tail {f g h : NFrame} : Moves f g → FrameMove g h → Moves f h

theorem Moves.single {f g : NFrame} (m : FrameMove f g) : Moves f g :=
  .tail (.refl f) m

theorem Moves.two {f g h : NFrame} (a : FrameMove f g)
    (b : FrameMove g h) : Moves f h :=
  .tail (.single a) b

theorem Moves.trans {f g h : NFrame} (a : Moves f g) (b : Moves g h) :
    Moves f h := by
  induction b with
  | refl => exact a
  | tail _ m ih => exact .tail ih m

/-- The induction every field instance uses: a relation that each move keeps is kept by a word. -/
theorem Moves.keeps (P : NFrame → Prop)
    (each : ∀ f g, FrameMove f g → P f → P g) {f g : NFrame} (w : Moves f g)
    (start : P f) : P g := by
  induction w with
  | refl => exact start
  | tail _ m ih => exact each _ _ m ih

theorem stepFrame_moves (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Moves f.frame (evaluatePrim.stepFrame interp m f yielding).fiber.frame := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events =>
    cases step with
    | running next => exact .single (.step _ _ _ _ hs)
    | finished exit => exact .single (.finish _ _ _ _ hs)

theorem finalizerOr_moves (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (exit : ExitV) :
    Moves f.frame (evaluatePrim.finalizerOr interp m f yielding exit).fiber.frame := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · exact .two (.pop _ _ _ _) (.answer _ _)
      · exact stepFrame_moves _ _ _ _
    · exact stepFrame_moves _ _ _ _

theorem withFiber_moves (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (action : NAction) :
    Moves f.frame
      (evaluatePrim.withFiber interp m f yielding action).fiber.frame := by
  cases action <;>
    simp only [evaluatePrim.withFiber,
      evaluatePrim.interruptAs, spawn, start, countdownPark, beginRace, RunFiber.park]
  all_goals repeat' first | exact .refl _ | exact .single (.answer _ _) | split
  all_goals first
    | exact .refl _
    | exact .single (.answer _ _)
    | exact .two (.mask _) (.answer _ _)
    | exact .two (.unmask _) (.answer _ _)
    | exact .single (.push _ _)
    | skip
  all_goals simp_all

theorem countdownPark_moves (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool) :
    Moves f.frame
      (countdownPark interp m f targets resumeWith failFast).2.1.frame := by
  unfold countdownPark
  dsimp only
  split
  · exact .single (.answer _ _)
  · simp only [RunFiber.park]
    exact .single (.push _ _)

theorem evaluatePrim_moves (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Moves f.frame (evaluatePrim interp m f yielding).fiber.frame := by
  simp only [evaluatePrim, registerRace, RunFiber.park]
  repeat' first
    | (split
       rename_i heq
       exact (congrArg (fun r => r.2.1.frame) heq) ▸ countdownPark_moves _ _ _ _ _ _)
    | exact stepFrame_moves _ _ _ _
    | exact finalizerOr_moves _ _ _ _ _
    | exact withFiber_moves _ _ _ _ _
    | exact .refl _
    | exact .single (.answer _ _)
    | exact .single (.push _ _)
    | split
  all_goals first
    | exact .refl _
    | exact .single (.answer _ _)
    | exact .single (.push _ _)
    | exact countdownPark_moves _ _ _ _ _ _
    | skip

end Probe.FrameMoves

/-! ## An instance: the guard's `interruptedCause` chain from the moves -/

namespace Probe.FrameMoves

open Effect4 Effect4.Machine Effect4.Program

/-- Each move keeps the recorded interrupt. -/
theorem move_interruptedCause {f g : NFrame} (m : FrameMove f g) :
    g.interruptedCause = f.interruptedCause := by
  cases m with
  | answer => rfl
  | push => rfl
  | step interp _ _ _ h =>
    exact Guard.Interruption.frame_step_interruptedCause interp _ _ (congrArg Prod.fst h)
  | finish => exact Guard.Interruption.frameExitState_interruptedCause _
  | pop => exact Guard.Interruption.getCont_interruptedCause_carried _ _ _ _
  | mask =>
    unfold FrameFiber.uninterruptible
    split <;> rfl
  | unmask =>
    unfold FrameFiber.interruptibleRegion FrameFiber.setFiberInterruptible
    split <;> rfl
  | pendingFailure => rfl

/-- The guard's `evaluatePrim_interruptedCause`, as an instance of the moves. -/
theorem evaluatePrim_interruptedCause' (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) :
    (evaluatePrim interp m f yielding).fiber.frame.interruptedCause = f.frame.interruptedCause :=
  (evaluatePrim_moves interp m f yielding).keeps (fun g => g.interruptedCause = f.frame.interruptedCause)
    (fun _ _ mv h => (move_interruptedCause mv).trans h) rfl

end Probe.FrameMoves

/-! ## The native wrappers and the loop's iteration -/

namespace Probe.FrameMoves

open Effect4 Effect4.Machine Effect4.Program

theorem exitScoped_moves (root : NativeEff) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (exit : ExitV) :
    Moves f.frame
      (exitScoped root m f yielding exit).fiber.frame := by
  unfold exitScoped
  dsimp only
  split
  · split
    · exact .two (.pop _ _ _ _) (.answer _ _)
    · exact .tail (.two (.pop _ _ _ _) (.answer _ _)) (.answer _ _)
  · exact evaluatePrim_moves _ _ _ _

theorem enterScoped_moves (root : NativeEff) (p : Point) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) :
    Moves f.frame (enterScoped root p m f yielding).fiber.frame :=
  .single (.answer _ _)

/-- One native evaluation edits the evaluated fiber's frame part by a word of moves. -/
theorem evaluateNative_moves (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    Moves f.frame (evaluateNative root m f yielding table).fiber.frame := by
  unfold evaluateNative
  split
  · split
    · exact enterScoped_moves _ _ _ _ _
    · exact evaluatePrim_moves _ _ _ _
  · exact exitScoped_moves _ _ _ _ _
  · exact exitScoped_moves _ _ _ _ _
  · exact evaluatePrim_moves _ _ _ _

/-- One iteration of the native loop: the loop's top, the op count, the yield injection, then
one native evaluation. -/
theorem iteration_moves (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Moves f.frame
      (iteration (evaluator := evaluatorFor root table) interp m f yielding).fiber.frame := by
  have top : Moves f.frame (countOp (runloopTop f)).frame := by
    unfold countOp runloopTop
    split
    · exact .single (.pendingFailure _)
    · exact .refl _
  unfold iteration
  dsimp only
  split
  · rename_i it h
    have hit : Moves f.frame it.fiber.frame := by
      unfold injectYield at h
      split at h
      · cases h
        exact top.tail (.answer _ _)
      · cases h
    exact hit.trans (evaluateNative_moves _ _ _ _ _)
  · exact top.trans (evaluateNative_moves _ _ _ _ _)

end Probe.FrameMoves
