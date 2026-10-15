import Test.Dogfood.Scenario.Atomic.RootHead
import Test.Dogfood.Scenario.Atomic.DaemonIteration
import Test.Dogfood.Scenario.Atomic.Initialization

/-!
Concept: store-typing R4.
Consumer: the actual Atomic initializer activation and root-role history producer.
The real entry point and mask suffix enter the root model without resetting source metadata.
The exact three-cell heap starts the same external stage world.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- The root keeps its current answer class and actual saved path to the unobserved root result. -/
def FrameAt (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  ∃ input, CodeAt root table world input frame.current ∧
    Effect4.Contracts.Path (Edge root table world) input .ordinary frame.stack

/-- Saved root frames preserve their captured source bindings at the supplied future counter. -/
theorem edge_future (root : NativeEff) (table : RowTable) (before after : StageWorld.World)
    (future : Future before after) (input output : StageWorld.Kind) (frame : NCode)
    (held : Edge root table before input output frame) : Edge root table after input output frame := by
  cases held with
  | saved held => exact .saved ⟨ViewSavedAt.future (model root table)
      (fun view => (interpAt root view table).toPrimInterp) (fun _ => future) held.held,
      held.inputOwned, held.outputOwned⟩
  | mapped ready held => exact .mapped trivial (DaemonGraph.edge_future root table before after future _ _ _ held)

/-- The actual saved path retains its root answer classes. -/
theorem path_owned (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (input output : StageWorld.Kind) (frames : List NCode)
    (held : Effect4.Contracts.Path (Edge root table world) input output frames)
    (owned : Owns output) : Owns input := by
  cases held with
  | nil => exact owned
  | cons first rest =>
    cases first with
    | saved held => exact held.inputOwned
    | mapped ready held => trivial

/-- A request write leaves the root's whole current frame valid at its unchanged counter. -/
theorem frame_counter (root : NativeEff) (table : RowTable) (before after : StageWorld.World)
    (future : Future before after) (counter : before.nextId = after.nextId)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (held : FrameAt root table before frame) :
    FrameAt root table after frame := by
  obtain ⟨input, code, saved⟩ := held
  have owns : Owns input := path_owned root table before input .ordinary frame.stack saved True.intro
  exact ⟨input, code_counter root table before input _ code after future counter owns,
    saved.map (edge_future root table before after future)⟩

/-- Actual root loop entry can replace its current code only by an unconstrained root failure. -/
theorem loop_top (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) (held : FrameAt root table world fiber.frame) :
    FrameAt root table world (countOp (runloopTop fiber)).frame := by
  obtain ⟨input, code, saved⟩ := held
  unfold countOp runloopTop
  split
  · exact ⟨input, .failure, saved⟩
  · exact ⟨input, code, saved⟩

/-- Actual addressed root interruption preserves its captured source and saved answer path. -/
theorem interruption_frame (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (fiber : SourceScope.SourceFiber) (cause : CauseV) (held : FrameAt root table world fiber.frame) :
    FrameAt root table world (interruptWithCause cause fiber).1.frame := by
  obtain ⟨input, code, saved⟩ := held
  unfold interruptWithCause
  split
  · exact ⟨input, code, saved⟩
  · dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
    split
    · split
      · exact ⟨input, code, saved⟩
      · exact ⟨input, .failure, saved⟩
    · exact ⟨input, code, saved⟩

/-- An actual ordinary root head retains its exact result path through the shared native connector. -/
theorem step_frame (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (view : List (FiberId × ExitV)) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (held : FrameAt built.program built.table world fiber.frame)
    (noSuccess : ∀ value, fiber.frame.current ≠ .success value)
    (noFailure : ∀ cause, fiber.frame.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.frame.current ≠ .sync thunk) :
    FrameAt built.program built.table world
      (evaluatePrim.stepFrame (interpAt built.program view built.table) machine fiber yielding).fiber.frame := by
  obtain ⟨input, code, saved⟩ := held
  exact External.Native.step_frame_running (model built.program built.table view)
    (interpAt built.program view built.table) (Edge built.program built.table) world input .ordinary
    machine fiber yielding saved
    (head built accepted world input fiber.frame.current code
      (path_owned built.program built.table world input .ordinary fiber.frame.stack saved True.intro) view)
    noSuccess noFailure noSync

/-- The actual bare initializer entry activates the numeric heap and exact root frame together. -/
theorem initializer_entry (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (entry : AnswerSlots.AllocationAdapter.EntryAt (RootCells.atomicAdapter built accepted) fragment machine fiber) :
    HeapAt initialWorld machine.state ∧ FrameAt built.program built.table initialWorld fiber.frame := by
  obtain ⟨point, output, current, exactEntry, saved⟩ := entry
  have env : point.env = [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩] := exactEntry.env
  have length : point.env.length = 3 := by rw [env]; rfl
  have refs : machine.state.refs = [Test.Dogfood.P4RateLimiter.windowVal 0 0 0,
      Store.Writes.account [], .list []] := exactEntry.contents.trans RootCells.atomic_values
  refine ⟨initial_heap machine.state refs, .ordinary, ?_, ?_⟩
  · rw [current]
    apply CodeAt.entry
    refine ⟨exactEntry.source, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [env]
      exact RootBindings.initial
    · rw [length]
      exact exactEntry.path
    · rw [length]
      exact Nat.le_refl 3
    · rw [length]
      decide
    · rw [length]
      rfl
  · exact AnswerSlots.AllocationAdapter.MaskSuffix.path (Edge built.program built.table initialWorld) .ordinary
      (mask_edge built.program built.table initialWorld .ordinary True.intro) fiber.frame.stack
      (AnswerSlots.AllocationAdapter.pending_root_path (RootCells.atomicAdapter built accepted) fragment
        ⟨fiber.id, machine.state, false⟩ rfl fiber.frame.stack output saved).2
end Test.Dogfood.Scenario.Atomic.RootGraph
