import Effect4.Api
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Moves — one evaluation edits a fiber's frame by a word of moves

The native evaluator (`evaluatePrim`, `exitScoped`, `enterScoped`, `evaluateNative`, and the
loop's `iteration`) edits the evaluated fiber's frame part in a few ways only. This module names
the moves. `Footprint.lean` classifies evaluations, and `Moves.lean` exposes their frame projection:

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

end Effect4.Program.Moves
