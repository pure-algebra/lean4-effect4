import Effect4.Api
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Moves — one evaluation edits a fiber's frame by a word of moves

The native evaluator (`evaluatePrim`, `exitScoped`, `enterScoped`, `evaluateNative`, and the
loop's `iteration`) edits the evaluated fiber's frame part in a few ways only. This module names
them and proves the classification once:

* **The moves** (`FrameMove`): answer a code, push a park's cancel frame, a step of the frame machine that goes
  on, a step that finishes (`frameExitState`), a pop (`getCont`), the mask, the unmask, and the
  loop's pending failure. A step and a finish carry the interpreter they used, so a word of moves
  (`Moves`) names no interpreter: the arms of one evaluation read different ones.
* **The classification** (`evaluatePrim_moves`, `exitScoped_moves`, `evaluateNative_moves`,
  `iteration_moves`): the evaluated fiber's frame after one evaluation is reached from its frame
  before by a word of moves.
* **The induction** (`Moves.keeps`): a property of frames that each move keeps is kept by every
  evaluation.

So a law about one frame field is a fact per move, most of them `rfl`. The per-field chains of the
guard bundle (`Guard/Interruption.lean`, `Guard/DeferredCause.lean`) are instances: each walks the
evaluator's levels for one field. Their replacement by instances is a later cleanup, landed beside
them first (the research note `docs/research/2026-10-11-machine-from-the-base/README.md`, §5).

Placement (AGENTS.md, Trust):

- concept `reactive-scheduling` (`docs/core/semantics.md` §2.4, invariants over execution traces,
  Owicki and Gries); the proposed registry claim is `evaluation-moves`, role structure, with
  pointer `iteration_moves`;
- reach: every native evaluation, at every machine, fiber, interpreter, row table and latch. It
  states the frame part only: the run fiber's other fields (park, context, dispatcher, op count),
  the machine and the other fibers are outside it;
- it does not establish which word an evaluation takes, any invariant, progress, or anything of a
  command beyond one evaluation;
- consumers: the field laws of the guard bundle (connectors in `Laws/Program/MovesConnect.lean`),
  then stack locality at the fiber machine, which `compiled_region_bracket`'s premise needs (R11),
  and the goals packet's fiber positions (G2).
-/

set_option autoImplicit false

namespace Effect4.Program.Moves

open Effect4 Effect4.Machine Effect4.Program

/-- The native frame part. -/
abbrev NFrame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann
/-- The native run fiber. -/
abbrev NFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
/-- The native machine's interpreter. -/
abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
/-- The frame machine's interpreter at the native alphabets. -/
abbrev NPrim := PrimInterp EffName EffThunk Val Err Defect FiberId Ann
/-- The frame machine's events at the native alphabets. -/
abbrev NEvent := FrameEvent EffName EffThunk Val Err Defect FiberId Ann

/-- The moves of one evaluation on the evaluated fiber's frame part. A step and a finish carry the
interpreter they ran with. -/
inductive FrameMove : NFrame → NFrame → Prop
  /-- The current code is replaced. -/
  | answer (f : NFrame) (c : NCode) : FrameMove f { f with current := c }
  /-- A park pushes its cancel frame, an `AsyncFinalizer`: the only frame an evaluation pushes
  outside the frame machine's own step. -/
  | push (f : NFrame) (name : EffName) :
      FrameMove f { f with stack := Prim.asyncFinalizer name :: f.stack }
  /-- A step of the frame machine that goes on. -/
  | step (interp : NPrim) (f g : NFrame) (events : List NEvent) :
      f.step interp = (FrameStep.running g, events) → FrameMove f g
  /-- A step of the frame machine that finishes, with the pop's retained state. -/
  | finish (interp : NPrim) (f : NFrame) (exit : ExitV) (events : List NEvent) :
      f.step interp = (FrameStep.finished exit, events) → FrameMove f (frameExitState f)
  /-- A pop: an exit meets the stack. -/
  | pop (f : NFrame) (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) :
      FrameMove f (f.getCont demand skip cause).fiber
  /-- The mask, with its restoring frame. -/
  | mask (f : NFrame) : FrameMove f f.uninterruptible
  /-- The unmask, with its re-masking frame. -/
  | unmask (f : NFrame) : FrameMove f f.interruptibleRegion.1
  /-- The loop's top meets a deferred interrupt. -/
  | pendingFailure (f : NFrame) :
      FrameMove f { f with deferredInterrupt := false, current := Prim.failure f.pendingCause }

/-- Words of moves, built at their end. -/
inductive Moves : NFrame → NFrame → Prop
  /-- The empty word. -/
  | refl (f : NFrame) : Moves f f
  /-- One more move at the end. -/
  | tail {f g h : NFrame} : Moves f g → FrameMove g h → Moves f h

/-- One move is a word. -/
theorem Moves.single {f g : NFrame} (m : FrameMove f g) : Moves f g :=
  .tail (.refl f) m

/-- Two moves are a word. -/
theorem Moves.two {f g h : NFrame} (a : FrameMove f g) (b : FrameMove g h) : Moves f h :=
  .tail (.single a) b

/-- Words compose. -/
theorem Moves.trans {f g h : NFrame} (a : Moves f g) (b : Moves g h) : Moves f h := by
  induction b with
  | refl => exact a
  | tail _ m ih => exact .tail ih m

/-- **The induction of every frame law**: a property that each move keeps is kept by a word. -/
@[semantics "reactive-scheduling"]
theorem Moves.keeps (P : NFrame → Prop) (each : ∀ f g, FrameMove f g → P f → P g)
    {f g : NFrame} (w : Moves f g) (start : P f) : P g := by
  induction w with
  | refl => exact start
  | tail _ m ih => exact each _ _ m ih

/-! ## The evaluator's levels -/

/-- The frame machine's step, delegated. -/
theorem stepFrame_moves (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Moves f.frame (evaluatePrim.stepFrame interp m f yielding).fiber.frame := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events =>
    cases step with
    | running next => exact .single (.step _ _ _ _ hs)
    | finished exit => exact .single (.finish _ _ _ _ hs)

/-- An exit meets the stack: a finalizer program after the pop, or the frame machine's step. -/
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

/-- The countdown park answers, or pushes its cancel frame. -/
theorem countdownPark_moves (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool) :
    Moves f.frame (countdownPark interp m f targets resumeWith failFast).2.1.frame := by
  unfold countdownPark
  dsimp only
  split
  · exact .single (.answer _ _)
  · simp only [RunFiber.park]
    exact .single (.push _ _)

/-- Every `withFiber` action: it answers, keeps the frame, parks through the countdown, or masks
or unmasks before it answers. -/
theorem withFiber_moves (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (action : NAction) :
    Moves f.frame (evaluatePrim.withFiber interp m f yielding action).fiber.frame := by
  cases action with
  | fork program options site =>
    simp only [evaluatePrim.withFiber, spawn, start]
    split <;> split <;> exact .single (.answer _ _)
  | forkIn program options scope site =>
    simp only [evaluatePrim.withFiber, spawn, start]
    split <;> exact .single (.answer _ _)
  | forkScoped program options site =>
    simp only [evaluatePrim.withFiber, spawn, start]
    split
    · split <;> exact .single (.answer _ _)
    · exact .single (.answer _ _)
  | ambientScope =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .single (.answer _ _)
  | runIn target scope => exact .single (.answer _ _)
  | interrupt target => exact .single (.answer _ _)
  | interruptAs target who =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split <;> exact .refl _
  | interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .single (.answer _ _)
  | interruptAll targets interruptor => exact .refl _
  | awaitAll targets => exact countdownPark_moves _ _ _ _ _ _
  | awaitAllFailFast targets => exact countdownPark_moves _ _ _ _ _ _
  | snapshotChildren => exact .single (.answer _ _)
  | awaitNewChildren snapshot => exact countdownPark_moves _ _ _ _ _ _
  | raceAll entrants site => exact .single (.answer _ _)
  | raceAllFirst entrants site => exact .single (.answer _ _)
  | setInterruptible body flag =>
    cases flag
    · exact .two (.mask _) (.answer _ _)
    · exact .two (.unmask _) (.answer _ _)
  | setContext context => exact .single (.answer _ _)
  | getContext => exact .single (.answer _ _)
  | getId => exact .single (.answer _ _)
  | closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split
    · exact .refl _
    · exact .single (.answer _ _)
  | closePar finalizers => exact .refl _
  | refuse cause => exact .single (.answer _ _)
  | dropObservers token => exact .single (.answer _ _)
  | cancelRace race =>
    simp only [evaluatePrim.withFiber]
    split
    · exact .single (.answer _ _)
    · exact .refl _
  | getInterruptible => exact .two (.mask _) (.answer _ _)

/-- **One primitive evaluation** edits the evaluated fiber's frame by a word of moves. -/
@[semantics "reactive-scheduling"]
theorem evaluatePrim_moves (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Moves f.frame (evaluatePrim interp m f yielding).fiber.frame := by
  unfold evaluatePrim
  split
  · simp only [RunFiber.park]
    exact .single (.answer _ _)
  · dsimp only
    split
    · exact .single (.answer _ _)
    · simp only [RunFiber.park]
      split
      · exact .single (.push _ _)
      · exact .refl _
  · split
    · exact .single (.answer _ _)
    · unfold registerRace
      split <;> exact .refl _
    · exact countdownPark_moves _ _ _ _ _ _
    · split
      · exact .refl _
      · split
        · exact .single (.answer _ _)
        · simp only [RunFiber.park]
          exact .single (.push _ _)
    · split
      · split
        · exact withFiber_moves _ _ _ _ _
        · exact stepFrame_moves _ _ _ _
      · split <;> exact .single (.answer _ _)
      · exact finalizerOr_moves _ _ _ _ _
      · exact finalizerOr_moves _ _ _ _ _
      · exact stepFrame_moves _ _ _ _

/-! ## The native wrappers and the loop's iteration -/

/-- The scoped exit pops, restores the context and answers; another exit is the primitive one. -/
theorem exitScoped_moves (root : NativeEff) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (exit : ExitV) :
    Moves f.frame (exitScoped root m f yielding exit).fiber.frame := by
  unfold exitScoped
  dsimp only
  split
  · split
    · exact .two (.pop _ _ _ _) (.answer _ _)
    · exact .tail (.two (.pop _ _ _ _) (.answer _ _)) (.answer _ _)
  · exact evaluatePrim_moves _ _ _ _

/-- The scoped entry answers with its region's `OnExit`. -/
theorem enterScoped_moves (root : NativeEff) (p : Point) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) :
    Moves f.frame (enterScoped root p m f yielding).fiber.frame :=
  .single (.answer _ _)

/-- **One native evaluation** edits the evaluated fiber's frame by a word of moves. -/
@[semantics "reactive-scheduling"]
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

/-- **One iteration of the native loop** (the loop's top, the op count, the yield injection,
then one native evaluation) edits the fiber's frame by a word of moves. The pointer of the
proposed claim `evaluation-moves`. -/
@[semantics "reactive-scheduling"]
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
    have injected : Moves f.frame it.fiber.frame := by
      unfold injectYield at h
      split at h
      · cases h
        exact top.tail (.answer _ _)
      · cases h
    exact injected.trans (evaluateNative_moves _ _ _ _ _)
  · exact top.trans (evaluateNative_moves _ _ _ _ _)

end Effect4.Program.Moves
