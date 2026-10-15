import Test.Dogfood.Scenario.Atomic.StageFrames
import Effect4.Laws.Program.Guard.DeferredCause

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the Atomic active native and contextual command producer for `shop_stages`.
Actual interruptions retain a non-fail reason, so no cleanup mask premise is needed for the requested observation.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageGraph
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- The actual interruption record contains no typed failure and retains an interrupt or defect reason. -/
def Recorded (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  ∀ cause, frame.interruptedCause = some cause →
    (∀ reason ∈ cause.reasons, reason.tag ≠ .fail) ∧ MarkedCause cause

/-- A real interruption retypes the actual request frame at its unchanged heap world. -/
theorem interruption_frame (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) (cause : CauseV)
    (held : FrameAt root table owner world fiber.frame) (recorded : Recorded fiber.frame)
    (untyped : ∀ reason ∈ cause.reasons, reason.tag ≠ .fail) (marked : MarkedCause cause) :
    FrameAt root table owner world (interruptWithCause cause fiber).1.frame := by
  obtain ⟨input, current, saved⟩ := held
  let accumulated := match fiber.frame.interruptedCause with
    | none => cause
    | some previous => Cause.combine previous cause
  have good : (∀ reason ∈ accumulated.reasons, reason.tag ≠ .fail) ∧ MarkedCause accumulated := by
    cases prior : fiber.frame.interruptedCause with
    | none => simpa only [accumulated, prior] using And.intro untyped marked
    | some previous =>
      simp only [accumulated, prior]
      have old := (recorded previous prior).1
      refine ⟨?_, MarkedCause.combine_right previous cause marked⟩
      intro reason member
      rcases Cause.combine_no_new_reason reason previous cause member with before | after
      · exact old reason before
      · exact untyped reason after
  unfold interruptWithCause
  split
  · exact ⟨input, current, saved⟩
  · dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
    split
    · split
      · exact ⟨input, current, saved⟩
      · refine ⟨input, .failure ?_, saved⟩
        cases prior : fiber.frame.interruptedCause <;>
          simpa only [accumulated, prior] using untyped_marked_cause world input accumulated good.1 good.2
    · exact ⟨input, current, saved⟩

/-- A real interruption records only the actual untyped marked causes supplied by its producer. -/
theorem interruption_recorded (fiber : SourceScope.SourceFiber) (cause : CauseV)
    (held : Recorded fiber.frame)
    (untyped : ∀ reason ∈ cause.reasons, reason.tag ≠ .fail) (marked : MarkedCause cause) :
    Recorded (interruptWithCause cause fiber).1.frame := by
  intro delivered actual
  unfold interruptWithCause at actual
  split at actual
  · exact held delivered actual
  · dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore] at actual
    split at actual
    · split at actual
      all_goals
        cases prior : fiber.frame.interruptedCause with
        | none =>
          simp only [prior, Option.some.injEq] at actual
          subst delivered
          exact ⟨untyped, marked⟩
        | some previous =>
          simp only [prior, Option.some.injEq] at actual
          subst delivered
          refine ⟨?_, MarkedCause.combine_right previous cause marked⟩
          intro reason member
          rcases Cause.combine_no_new_reason reason previous cause member with old | added
          · exact (held previous prior).1 reason old
          · exact untyped reason added
    · cases prior : fiber.frame.interruptedCause with
      | none =>
        simp only [prior, Option.some.injEq] at actual
        subst delivered
        exact ⟨untyped, marked⟩
      | some previous =>
        simp only [prior, Option.some.injEq] at actual
        subst delivered
        refine ⟨?_, MarkedCause.combine_right previous cause marked⟩
        intro reason member
        rcases Cause.combine_no_new_reason reason previous cause member with old | added
        · exact (held previous prior).1 reason old
        · exact untyped reason added

/-- Actual deferred loop entry consumes its recorded non-fail cause at the same answer endpoint. -/
theorem loop_top (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) (held : FrameAt root table owner world fiber.frame)
    (recorded : Recorded fiber.frame) (consistent : Guard.DeferredCause.DeferredCause fiber.frame) :
    FrameAt root table owner world (countOp (runloopTop fiber)).frame := by
  obtain ⟨input, current, saved⟩ := held
  unfold countOp runloopTop
  split
  · rename_i deferred
    cases prior : fiber.frame.interruptedCause with
    | none =>
      have present := consistent deferred
      rw [prior] at present
      cases present
    | some cause =>
      have good := recorded cause prior
      refine ⟨input, .failure ?_, saved⟩
      simpa only [FrameFiber.pendingCause, prior, Option.getD_some] using
        untyped_marked_cause world input cause good.1 good.2
  · exact ⟨input, current, saved⟩

/-- The shared native frame-move producer retains the actual recorded interruption witness. -/
theorem native_recorded (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (held : Recorded fiber.frame) :
    Recorded (evaluateNative root machine fiber yielding table).fiber.frame := by
  intro cause recorded
  rw [Guard.Interruption.evaluateNative_interruptedCause root table machine fiber yielding] at recorded
  exact held cause recorded

/-- The same shared iteration producer retains the record through loop-top and yield injection. -/
theorem iteration_recorded (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (held : Recorded fiber.frame) :
    letI := evaluatorFor root table
    Recorded (iteration (interpOf root table) machine fiber yielding).fiber.frame := by
  letI := evaluatorFor root table
  intro cause recorded
  rw [Guard.Interruption.iteration_interruptedCause root table machine fiber yielding] at recorded
  exact held cause recorded
end Test.Dogfood.Scenario.Atomic.StageGraph
