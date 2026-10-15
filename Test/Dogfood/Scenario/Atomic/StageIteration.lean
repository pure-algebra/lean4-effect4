import Test.Dogfood.Scenario.Atomic.StagePrimitive

/-!
Concept: reactive-scheduling R11 and store-typing R4.
Consumer: the Atomic request loop command in the coupled stage history.
The actual charged entry and optional scheduler wrapper use the same checked native producer.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Charging loop entry retains its actual recorded interruption. -/
theorem top_recorded (fiber : SourceScope.SourceFiber) (recorded : Recorded fiber.frame) :
    Recorded (countOp (runloopTop fiber)).frame := by
  intro cause prior
  change (runloopTop fiber).frame.interruptedCause = some cause at prior
  rw [Guard.Interruption.runloopTop_interruptedCause] at prior
  exact recorded cause prior

/-- Actual scheduler injection preserves the original request phase in its saved constant callback. -/
theorem injected_frame (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (held : FrameAt root table owner world frame) :
    FrameAt root table owner world {frame with current := .onSuccessConst (.yieldNowWith 0) frame.current} := by
  obtain ⟨input, code, saved⟩ := held
  exact ⟨input, .pausing (path_input_owned root table owner world input (.finalized owner) frame.stack saved rfl) code, saved⟩

/-- Every actual charged request iteration joins one next heap with its live result or completed exit. -/
theorem iteration_result (root : NativeEff) (table : RowTable) (owner : Nat) (member : owner ∈ requests)
    (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table owner world fiber.frame) (heap : HeapAt world machine.state)
    (recorded : Recorded fiber.frame) (consistent : Guard.DeferredCause.DeferredCause fiber.frame) :
    letI := evaluatorFor root table
    ∃ next, Future world next ∧ RequestChange world next owner ∧
      HeapAt next (iteration (interpOf root table) machine fiber yielding).machine.state ∧
      External.Native.ResultAt (model root table owner machine.completedExits) (Edge root table owner) next (.finalized owner)
        (iteration (interpOf root table) machine fiber yielding) := by
  letI := evaluatorFor root table
  have top := loop_top root table owner world fiber held recorded consistent
  have topRecorded := top_recorded fiber recorded
  have topConsistent : Guard.DeferredCause.DeferredCause (countOp (runloopTop fiber)).frame :=
    Guard.DeferredCause.runloopTop_deferredCause fiber consistent
  unfold iteration
  dsimp only
  split
  · rename_i result injected
    unfold injectYield at injected
    split at injected
    · cases injected
      exact native_result root table owner member world
        (machine.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}}
        true (injected_frame root table owner world _ top) heap topRecorded topConsistent
    · cases injected
  · exact native_result root table owner member world machine (countOp (runloopTop fiber)) yielding
      top heap topRecorded topConsistent
end Test.Dogfood.Scenario.Atomic.StageGraph
