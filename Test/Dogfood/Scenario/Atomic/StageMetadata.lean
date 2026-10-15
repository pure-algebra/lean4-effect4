import Test.Dogfood.Scenario.Atomic.RootPrimitive
import Test.Dogfood.Scenario.Atomic.StageRows
import Test.Dogfood.Scenario.Atomic.StageObservation
import Effect4.Laws.Program.ParkedShapeRun

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: the actual Atomic coupled machine assertion and contextual message producer.
Stored rows retain recorded causes, published exits, childlessness and observer reply owners.
The shared whole-row primitive proof supplies their actual native transport.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Only root or daemon waits can receive another fiber's possibly failing exit. -/
inductive ObserverAt : Observer → Prop
  | await (waiter : FiberId) (token : Nat) (mode : Supervision.ObserverMode) (small : waiter.value < 2) :
      ObserverAt (.resumeAwait waiter token mode)
  | countdown (waiter : FiberId) (token : Nat) (small : waiter.value < 2) :
      ObserverAt (.countdown waiter token)
  | untrack (parent : FiberId) : ObserverAt (.untrackChild parent)
  | drop (scope key : Nat) : ObserverAt (.dropScopeFinalizer scope key)

/-- The non-frame parts needed by actual request publication and callback admission. -/
structure RowAt (world : StageWorld.World) (fiber : SourceScope.SourceFiber) : Prop where
  recorded : ∀ owner ∈ requests, fiber.id = ⟨owner + 1⟩ → StageGraph.Recorded fiber.frame
  published : ∀ owner ∈ requests, fiber.id = ⟨owner + 1⟩ → FinalExitAt world owner fiber.exit
  childless : fiber.id ≠ ⟨0⟩ → fiber.children = []
  observers : ∀ observer ∈ fiber.observers, ObserverAt observer

/-- Unchanged rows retain their certified published observations at the actual next world. -/
theorem RowAt.future (before after : StageWorld.World) (future : Future before after)
    (fiber : SourceScope.SourceFiber) (held : RowAt before fiber) : RowAt after fiber :=
  ⟨held.recorded, fun owner member same => final_exit_future before after future owner fiber.exit
    (held.published owner member same), held.childless, held.observers⟩

/-- Every actual newly allocated child starts without an exit, children, observers or recorded cause. -/
theorem RowAt.birth (world : StageWorld.World) (id : FiberId) (program : NCode) (flag : Bool)
    (budget : Nat × Bool) (context : Ctx) :
    RowAt world (RunFiber.make id program flag budget context) := by
  constructor
  · intro owner member same cause found
    cases found
  · intro owner member same
    exact True.intro
  · intro different
    rfl
  · intro observer member
    cases member

/-- Actual native actor metadata uses the existing evaluation footprint and recorded-cause producer. -/
theorem RowAt.native (root : NativeEff) (table : RowTable) (before after : StageWorld.World)
    (future : Future before after) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (held : RowAt before fiber) :
    RowAt after (evaluateNative root machine fiber yielding table).fiber := by
  have fields := Moves.evaluateNative_footprint root table machine fiber yielding
  constructor
  · intro owner member same
    rw [fields.id] at same
    exact StageGraph.native_recorded root table machine fiber yielding (held.recorded owner member same)
  · intro owner member same
    rw [fields.id] at same
    rw [fields.exit]
    exact final_exit_future before after future owner fiber.exit (held.published owner member same)
  · intro different
    rw [fields.id] at different
    rw [fields.children]
    exact held.childless different
  · rw [fields.observers]
    exact held.observers

/-- Every stored row retains the metadata required by its actual future publication. -/
def RowsAt (world : StageWorld.World) (machine : NativeMachine) : Prop :=
  ∀ fiber ∈ machine.fibers, RowAt world fiber

/-- The generalized existing primitive proof transports whole stored rows and seeds actual births. -/
theorem RowsAt.primitive (root : NativeEff) (fragment : SourceScope.Fragment root) (table : RowTable)
    (view : List (FiberId × ExitV)) (before after : StageWorld.World) (future : Future before after)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (source : SourceScope.FrameAt root fiber.frame) (held : RowsAt before machine) :
    RowsAt after (evaluatePrim (interpAt root view table) machine fiber yielding).machine := by
  have oldRows : ∀ row ∈ machine.fibers, RowAt after row := fun row member =>
    RowAt.future before after future row (held row member)
  apply NativeFrameRows.primitive_row_facts (interpAt root view table) machine fiber yielding _
    (Moves.evaluatePrim_producer (interpAt root view table) machine fiber yielding) (RowAt after) oldRows
  intro thunk action current unparked found
  have thunkAt : SourceScope.ThunkAt root thunk := by
    have owned := source.1
    rw [current] at owned
    exact owned
  have programs := SourceScope.interp_action_at root fragment view table thunk action thunkAt found
  exact SourceScope.with_fiber_rows root view table (fun _ => True) (RowAt after) machine fiber yielding action oldRows
    (SourceScope.ActionProgramsAt.mono root action programs (fun _ _ _ => True.intro))
    (fun id program flag budget context _ => RowAt.birth after id program flag budget context)

/-- Installing the evaluated row preserves every other stored row's metadata. -/
theorem RowsAt.update (world : StageWorld.World) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (held : RowsAt world machine) (actor : RowAt world fiber) : RowsAt world (machine.update fiber) := by
  intro row member
  obtain ⟨old, present, equal⟩ := List.mem_map.mp member
  rw [← equal]
  change RowAt world (if old.id = fiber.id then fiber else old)
  split
  · exact actor
  · exact held old present

end Test.Dogfood.Scenario.Atomic.StageConfiguration
