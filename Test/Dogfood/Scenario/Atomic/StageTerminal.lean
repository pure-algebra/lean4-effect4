import Test.Dogfood.Scenario.Atomic.StageCharged
import Effect4.Laws.Program.MovesConnect

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Consumer: Atomic's actual finish command and its coupled stage history.
The root's child interruption program starts at the actual empty terminal stack.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- The authored middleware child interruption retains the root's ordinary terminal endpoint. -/
theorem root_children_frame (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (children : List FiberId) (exit : ExitV)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (empty : frame.stack = []) :
    RootGraph.FrameAt root table world
      { frame with deferredInterrupt := false, current := .onSuccess (.withFiber (.store (.act (.interruptAll children none)))) (.restore exit) } := by
  refine ⟨.ordinary, ?_, ?_⟩
  · refine .bound (input := .ordinary) True.intro (.ignored (.interruptAll children none)) ?_
    intro after future view value good
    cases exit with
    | success answer => exact .ignored (.success answer)
    | failure cause => exact .ignored (.failure cause)
  · rw [empty]
    exact .nil _

/-- Actual middleware re-entry installs the terminal root program at the same stage world. -/
theorem Configuration.exit_children (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (exit : ExitV)
    (held : Configuration root table world machine) (member : fiber ∈ machine.fibers)
    (identity : fiber.id = ⟨0⟩) (empty : fiber.frame.stack = []) :
    Configuration root table world
      (exitFiber.exitInterruptChildren (interpOf root table) machine { fiber with running := false } exit).1 := by
  have metadata := held.metadata fiber member
  unfold exitFiber.exitInterruptChildren
  apply Configuration.emit
  apply held.update root table world machine
  · exact Or.inl (.root identity (root_children_frame root table world fiber.children exit fiber.frame empty))
  · exact ⟨metadata.recorded, metadata.published, metadata.childless, metadata.observers⟩

/-- Publishing the actual completed exit records exactly its certified request observation. -/
theorem Configuration.publish (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (exit : ExitV)
    (held : Configuration root table world machine) (member : fiber ∈ machine.fibers)
    (completed : CompletedAt world fiber.id exit) :
    Configuration root table world (machine.update (fiber.publish exit)) := by
  have metadata := held.metadata fiber member
  apply held.update root table world machine
  · exact Or.inr (Or.inl rfl)
  · refine ⟨metadata.recorded, ?_, metadata.childless, metadata.observers⟩
    exact fun owner requested identity => completed owner requested identity

/-- Clearing a published row retains its recorded exit and removes its child and observer lists. -/
theorem Configuration.clear (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (held : Configuration root table world machine) (member : fiber ∈ machine.fibers)
    (exited : fiber.exit.isSome = true) :
    Configuration root table world (machine.update (fiber.cleared (interpOf root table))) := by
  have metadata := held.metadata fiber member
  apply held.update root table world machine
  · exact Or.inr (Or.inl exited)
  · refine ⟨metadata.recorded, metadata.published, ?_, ?_⟩
    · intro different
      rfl
    · intro observer present
      cases present

/-- The actual publication branch retains the completed stage observation through clearing. -/
theorem Configuration.exit_store (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (exit : ExitV)
    (held : Configuration root table world machine) (member : fiber ∈ machine.fibers)
    (completed : CompletedAt world fiber.id exit) :
    Configuration root table world
      (exitFiber.exitStore (interpOf root table) machine { fiber with running := false } exit).1 := by
  have metadata := held.metadata fiber member
  have published : Configuration root table world
      (machine.update (({fiber with running := false}).publish exit)) := by
    apply held.update root table world machine
    · exact Or.inr (Or.inl rfl)
    · exact ⟨metadata.recorded, fun owner requested identity => completed owner requested identity,
        metadata.childless, metadata.observers⟩
  have emitted := published.emit root table world _ [RunEvent.exited fiber.id exit]
  unfold exitFiber.exitStore
  dsimp only
  split
  · apply emitted.update root table world
    · exact Or.inr (Or.inl rfl)
    · refine ⟨metadata.recorded, fun owner requested identity => completed owner requested identity, ?_, ?_⟩
      · intro different
        rfl
      · intro observer present
        cases present
  · exact emitted

/-- The actual finish command publishes its certified exit or enters the root's child cleanup. -/
theorem Configuration.finish (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (exit : ExitV)
    (held : Configuration root table world machine) (member : fiber ∈ machine.fibers)
    (completed : CompletedAt world fiber.id exit) (empty : fiber.frame.stack = []) :
    Configuration root table world
      (exitFiber (interpOf root table) machine { fiber with running := false } exit).1 := by
  unfold exitFiber
  split
  · rename_i children
    have rootActor : fiber.id = ⟨0⟩ := by
      by_cases identity : fiber.id = ⟨0⟩
      · exact identity
      · have noChildren := (held.metadata fiber member).childless identity
        simp only [noChildren, List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true] at children
    exact held.exit_children root table world machine fiber exit member rootActor empty
  · exact held.exit_store root table world machine fiber exit member completed

/-- The existing actual finishing witness gives exactly the stack needed by middleware re-entry. -/
theorem native_finished_empty (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (finished : (evaluateNative root machine fiber yielding table).outcome = .finished exit) :
    (evaluateNative root machine fiber yielding table).fiber.frame.stack = [] :=
  (Moves.evaluateNative_parking root table machine fiber yielding).finished.stack finished

end Test.Dogfood.Scenario.Atomic.StageConfiguration
