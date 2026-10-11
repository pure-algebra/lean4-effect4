import Effect4.Laws.Program.Footprint

/-!
Concept: reactive-scheduling, the frame projection of the proposed `evaluation-moves` claim.
The move relation and its induction belong to `FrameMoves.lean`.
The evaluator classification belongs to `Footprint.lean`; these existing interfaces project its frame word.
Consumers: guard frame invariants and the native stack-locality proofs.
These projections establish no progress, command closure, or source-code ownership.
-/
set_option autoImplicit false
namespace Effect4.Program.Moves
open Effect4 Effect4.Machine Effect4.Program

/-- The frame machine's step, delegated. -/
theorem stepFrame_moves (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Moves f.frame (evaluatePrim.stepFrame interp m f yielding).fiber.frame :=
  (stepFrame_footprint interp m f yielding).frame

/-- An exit meets the stack: a finalizer program after the pop, or the frame machine's step. -/
theorem finalizerOr_moves (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (exit : ExitV) :
    Moves f.frame (evaluatePrim.finalizerOr interp m f yielding exit).fiber.frame :=
  (finalizerOr_footprint interp m f yielding exit).frame

/-- The countdown park answers, or pushes its cancel frame. -/
theorem countdownPark_moves (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool) :
    Moves f.frame (countdownPark interp m f targets resumeWith failFast).2.1.frame :=
  (countdownPark_footprint interp m f targets resumeWith failFast).frame

/-- Every `withFiber` action: it answers, keeps the frame, parks through the countdown, or masks
or unmasks before it answers. -/
theorem withFiber_moves (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (action : NAction) :
    Moves f.frame (evaluatePrim.withFiber interp m f yielding action).fiber.frame :=
  (withFiber_footprint interp m f yielding action).frame

/-- **One primitive evaluation** edits the evaluated fiber's frame by a word of moves. -/
@[semantics "reactive-scheduling"]
theorem evaluatePrim_moves (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Moves f.frame (evaluatePrim interp m f yielding).fiber.frame :=
  (evaluatePrim_footprint interp m f yielding).frame

/-! ## The native wrappers and the loop's iteration -/

/-- The scoped exit pops, restores the context and answers; another exit is the primitive one. -/
theorem exitScoped_moves (root : NativeEff) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (exit : ExitV) :
    Moves f.frame (exitScoped root m f yielding exit).fiber.frame :=
  (exitScoped_footprint root m f yielding exit).frame

/-- The scoped entry answers with its region's `OnExit`. -/
theorem enterScoped_moves (root : NativeEff) (p : Point) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) :
    Moves f.frame (enterScoped root p m f yielding).fiber.frame :=
  .single (.answer _ _)

/-- **One native evaluation** edits the evaluated fiber's frame by a word of moves. -/
@[semantics "reactive-scheduling"]
theorem evaluateNative_moves (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    Moves f.frame (evaluateNative root m f yielding table).fiber.frame :=
  (evaluateNative_footprint root table m f yielding).frame

/-- **One iteration of the native loop** (the loop's top, the op count, the yield injection,
then one native evaluation) edits the fiber's frame by a word of moves. The pointer of the
proposed claim `evaluation-moves`. -/
@[semantics "reactive-scheduling"]
theorem iteration_moves (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Moves f.frame
      (iteration (evaluator := evaluatorFor root table) interp m f yielding).fiber.frame :=
  (iteration_footprint root table interp m f yielding).frame

end Effect4.Program.Moves
