import Test.Dogfood.Scenario.Atomic.StageIteration
import Effect4.Laws.Program.PrimitiveDispatcher

/-!
Concept: store-typing R4.
Consumer: the Atomic active configuration's nonacting rows and queued scheduler replies.
A request primitive retains the exact stored rows, including their published exits.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Actual request native evaluation retains every stored row and certifies its scheduled unit replies. -/
theorem native_rows (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : FrameAt root table owner world fiber.frame) (recorded : Recorded fiber.frame)
    (P : Task EffName EffThunk Val Err Defect FiberId Ann → Prop)
    (reply : ∀ id token, P (.resume id token (.success .unit)))
    (tasks : DispatcherPredicate.All P fiber.dispatcher) :
    (evaluateNative root machine fiber yielding table).machine.fibers = machine.fibers ∧
      DispatcherPredicate.All P (evaluateNative root machine fiber yielding table).fiber.dispatcher := by
  rw [native_primitive_eq root table owner world machine fiber yielding held recorded]
  obtain ⟨input, code, saved⟩ := held
  have ordinary := ordinary_shape root table owner machine.completedExits world input fiber.frame.current code
  exact Moves.evaluatePrim_dispatcher (interpAt root machine.completedExits table) machine fiber yielding
    P reply tasks ordinary.1 ordinary.2.1

end Test.Dogfood.Scenario.Atomic.StageGraph
