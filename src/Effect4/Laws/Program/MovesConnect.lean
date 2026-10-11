import Effect4.Laws.Program.Moves
import Effect4.Laws.Program.Parking
import Effect4.Laws.Program.Guard.Interruption
import Effect4.Laws.Program.Guard.DeferredCause
import Effect4.Laws.Machine.MaskRuns

/-!
# Laws.Program.MovesConnect — frame laws as instances of the moves

Each law here was proved before by its own chain through the evaluator's levels. Here each is one
fact per move (`FrameMove`, `Laws/Program/Moves.lean`) and one use of `Moves.keeps`. The statements
are those of the existing chains, so the chains can be replaced by these proofs in place:

* the recorded interrupt (`Guard.Interruption.evaluateNative_interruptedCause`,
  `Guard.Interruption.iteration_interruptedCause`);
* the deferred bit's cause (`Guard.DeferredCause.evaluateNative_deferredCause`,
  `Guard.DeferredCause.iteration_deferredCause`);
* the saved mask's chain (`MaskChain`), the evaluation half of `MaskRuns`'s
  `evaluateNative_keepsMask`.

Placement (AGENTS.md, Trust): concept `reactive-scheduling`; each theorem is a connector of the
proposed claim `evaluation-moves` to a law already proved, and serves that law's claims. Reach:
every native evaluation and iteration. It establishes nothing beyond the laws it restates.
The replacement of the old chains is the cleanup of the research note
`docs/research/2026-10-11-machine-from-the-base/README.md`, §5.3.
-/

set_option autoImplicit false

namespace Effect4.Program.Moves

open Effect4 Effect4.Machine Effect4.Program

/-! ## The recorded interrupt -/

/-- Each move keeps the recorded interrupt. -/
theorem move_interruptedCause {f g : NFrame} (m : FrameMove f g) :
    g.interruptedCause = f.interruptedCause :=
  Guard.Interruption.move_interruptedCause m

/-- A word keeps the recorded interrupt. -/
theorem Moves.interruptedCause {f g : NFrame} (w : Moves f g) :
    g.interruptedCause = f.interruptedCause :=
  w.keeps (fun h => h.interruptedCause = f.interruptedCause)
    (fun _ _ mv kept => (move_interruptedCause mv).trans kept) rfl

/-- Connector of `Guard.Interruption.evaluateNative_interruptedCause`. -/
@[semantics "reactive-scheduling"]
theorem evaluateNative_interruptedCause (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    (evaluateNative p m f yielding table).fiber.frame.interruptedCause =
      f.frame.interruptedCause :=
  (evaluateNative_moves p table m f yielding).interruptedCause

/-- Connector of `Guard.Interruption.iteration_interruptedCause`. -/
@[semantics "reactive-scheduling"]
theorem iteration_interruptedCause (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    (iteration (interpOf p table) m f yielding).fiber.frame.interruptedCause =
      f.frame.interruptedCause :=
  (iteration_moves p table (interpOf p table) m f yielding).interruptedCause

/-! ## The deferred bit's cause -/

/-- Each move keeps "a deferred interrupt has a recorded cause". -/
theorem move_deferredCause {f g : NFrame} (m : FrameMove f g)
    (kept : Guard.DeferredCause.DeferredCause f) : Guard.DeferredCause.DeferredCause g :=
  Guard.DeferredCause.move_deferredCause m kept

/-- Connector of `Guard.DeferredCause.evaluateNative_deferredCause`. -/
@[semantics "reactive-scheduling"]
theorem evaluateNative_deferredCause (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (hf : f.frame.deferredInterrupt = true → f.frame.interruptedCause.isSome = true) :
    (evaluateNative p m f yielding table).fiber.frame.deferredInterrupt = true →
      (evaluateNative p m f yielding table).fiber.frame.interruptedCause.isSome = true :=
  (evaluateNative_moves p table m f yielding).keeps Guard.DeferredCause.DeferredCause
    (fun _ _ mv kept => move_deferredCause mv kept) hf

/-- Connector of `Guard.DeferredCause.iteration_deferredCause`. -/
@[semantics "reactive-scheduling"]
theorem iteration_deferredCause (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (hf : f.frame.deferredInterrupt = true → f.frame.interruptedCause.isSome = true) :
    letI := evaluatorFor p table
    (iteration (interpOf p table) m f yielding).fiber.frame.deferredInterrupt = true →
      (iteration (interpOf p table) m f yielding).fiber.frame.interruptedCause.isSome = true :=
  (iteration_moves p table (interpOf p table) m f yielding).keeps
    Guard.DeferredCause.DeferredCause (fun _ _ mv kept => move_deferredCause mv kept) hf

/-! ## The finishing outcome -/

/-- The finishing witness gives the empty returned stack.
Consumer: `evaluateNative_keepsMask`, then the region bracket. -/
theorem FinishOrigin.stack {it : ParkIter} (origin : FinishOrigin it) {exit : ExitV}
    (finished : it.outcome = .finished exit) : it.fiber.frame.stack = [] := by
  obtain ⟨interp, frame, events, step, returned⟩ := origin exit finished
  rw [returned]
  exact Machine.step_finished_stack interp frame exit (congrArg Prod.fst step)

/-! ## The saved mask's chain -/

/-- Each move keeps the saved mask's chain at a base. -/
theorem move_maskChain (base : Bool) {f g : NFrame} (m : FrameMove f g)
    (kept : FrameFiber.MaskChain base f.interruptible f.stack) :
    FrameFiber.MaskChain base g.interruptible g.stack := by
  cases m with
  | answer => exact kept
  | push => exact kept
  | step interp _ _ _ h => exact FrameFiber.step_maskChain base interp _ kept _ (congrArg Prod.fst h)
  | finish => exact Machine.frameExitState_maskChain base _ kept
  | pop => exact FrameFiber.getCont_maskChain base _ _ _ _ kept
  | mask => exact FrameFiber.uninterruptible_maskChain base _ kept
  | unmask => exact FrameFiber.interruptibleRegion_maskChain base _ kept
  | pendingFailure => exact kept

/-- **One native evaluation keeps the saved mask's chain**: the evaluation half of
`MaskRuns`, as an instance of the moves. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem evaluateNative_maskChain (base : Bool) (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (kept : FrameFiber.MaskChain base f.frame.interruptible f.frame.stack) :
    FrameFiber.MaskChain base (evaluateNative p m f yielding table).fiber.frame.interruptible
      (evaluateNative p m f yielding table).fiber.frame.stack :=
  (evaluateNative_moves p table m f yielding).keeps
    (fun g => FrameFiber.MaskChain base g.interruptible g.stack)
    (fun _ _ mv chain => move_maskChain base mv chain) kept

end Effect4.Program.Moves
