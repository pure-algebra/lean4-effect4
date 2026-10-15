import Test.Dogfood.Scenario.Atomic.StageResults

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: the actual Atomic native configuration join.
Existing primitive producers retain stored rows and the allocation counter for nonroot actors.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.DaemonGraph
open Effect4 Effect4.Machine Effect4.Program

/-- Actual daemon evaluation retains every supplied stored-row assertion. -/
theorem native_rows (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table world fiber.frame) (G : SourceScope.SourceFiber → Prop)
    (rows : ∀ row ∈ machine.fibers, G row) :
    ∀ row ∈ (evaluateNative root machine fiber yielding table).machine.fibers, G row := by
  rw [native_primitive_eq root table world machine fiber yielding held]
  apply NativeFrameRows.primitive_row_facts (interpAt root machine.completedExits table) machine fiber yielding _
    (Moves.evaluatePrim_producer _ _ _ _) G rows
  intro thunk action current unparked found
  have same := (action_frame root table world machine.completedExits machine fiber yielding thunk action held current found).2.1
  rw [same]
  exact rows

/-- The daemon's actual administrative actions allocate no fiber identity. -/
theorem native_counter (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table world fiber.frame) :
    (evaluateNative root machine fiber yielding table).machine.nextId = machine.nextId := by
  rw [native_primitive_eq root table world machine fiber yielding held]
  apply Moves.evaluatePrim_nextId_of_actions
  intro thunk action current unparked found
  rcases action_shape root table thunk (current ▸ held.1) with ⟨targets, who, rfl⟩ | ⟨token, rfl⟩
  · change some (.interruptAll targets who) = some action at found
    cases found
    rfl
  · change some (.dropObservers token) = some action at found
    cases found
    rfl
end Test.Dogfood.Scenario.Atomic.DaemonGraph

namespace Test.Dogfood.Scenario.Atomic.StageGraph
open Effect4 Effect4.Machine Effect4.Program

/-- Actual request evaluation allocates no fiber identity, including inside its finalizer. -/
theorem native_counter (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table owner world fiber.frame) (recorded : Recorded fiber.frame) :
    (evaluateNative root machine fiber yielding table).machine.nextId = machine.nextId := by
  rw [native_primitive_eq root table owner world machine fiber yielding held recorded]
  obtain ⟨input, code, saved⟩ := held
  have ordinary := ordinary_shape root table owner machine.completedExits world input fiber.frame.current code
  exact Moves.evaluatePrim_nextId (interpAt root machine.completedExits table) machine fiber yielding ordinary.1 ordinary.2.1
end Test.Dogfood.Scenario.Atomic.StageGraph
