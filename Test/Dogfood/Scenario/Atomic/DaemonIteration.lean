import Test.Dogfood.Scenario.Atomic.DaemonNative
import Effect4.Laws.Machine.AnswerFlowNativeIteration

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: the Atomic whole native iteration and coupled history producer.
The actual daemon frame retains its saved path through ordinary execution and scheduler injection.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.DaemonGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

def FrameAt (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  CodeAt root table frame.current ∧ Effect4.Contracts.Path (Edge root table world) () () frame.stack

/-- Request writes retain the daemon's actual saved callbacks and recursive loop names. -/
theorem edge_future (root : NativeEff) (table : RowTable) (before after : StageWorld.World)
    (future : Future before after) (input output : Unit) (frame : NCode)
    (held : Edge root table before input output frame) : Edge root table after input output frame := by
  cases held with
  | saved owned => exact .saved (ViewSavedAt.future (model root table)
      (fun view => (interpAt root view table).toPrimInterp) (fun _ => future) owned)
  | loop cursor owned => exact .loop cursor owned
  | iterator cursor impossible => cases impossible

/-- The unchanged daemon frame remains valid at the same future request world. -/
theorem frame_future (root : NativeEff) (table : RowTable) (before after : StageWorld.World)
    (future : Future before after) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (held : FrameAt root table before frame) : FrameAt root table after frame :=
  ⟨held.1, held.2.map (edge_future root table before after future)⟩

/-- Native loop-top interruption and operation charging retain the daemon's actual frame path. -/
theorem loop_top (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) (held : FrameAt root table world fiber.frame) :
    FrameAt root table world (countOp (runloopTop fiber)).frame := by
  unfold countOp runloopTop
  split
  · exact ⟨.failure _, held.2⟩
  · exact held

/-- Actual addressed daemon interruption retains its ignored-answer saved path. -/
theorem interruption_frame (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) (cause : CauseV) (held : FrameAt root table world fiber.frame) :
    FrameAt root table world (interruptWithCause cause fiber).1.frame := by
  unfold interruptWithCause
  split
  · exact held
  · dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
    split
    · split
      · exact held
      · exact ⟨.failure _, held.2⟩
    · exact held

/-- Scheduler injection retains the actual daemon primitive under its saved constant callback. -/
theorem injected_code (root : NativeEff) (table : RowTable) (code : NCode) (held : CodeAt root table code) :
    CodeAt root table (.onSuccessConst (.yieldNowWith 0) code) := .constant (.pause 0) held

/-- The actual ordinary daemon native step uses the shared frame connector. -/
theorem step_frame (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table world fiber.frame)
    (noSuccess : ∀ value, fiber.frame.current ≠ .success value)
    (noFailure : ∀ cause, fiber.frame.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.frame.current ≠ .sync thunk) :
    FrameAt root table world (evaluatePrim.stepFrame (interpAt root view table) machine fiber yielding).fiber.frame := by
  obtain ⟨result, incoming, code, saved⟩ := External.Native.step_frame (model root table view)
    (interpAt root view table) (Edge root table) world () () machine fiber yielding held.1 held.2
    (head root table world fiber.frame.current held.1 view) noSuccess noFailure noSync
  cases result
  cases incoming
  exact ⟨code, saved⟩
end Test.Dogfood.Scenario.Atomic.DaemonGraph
