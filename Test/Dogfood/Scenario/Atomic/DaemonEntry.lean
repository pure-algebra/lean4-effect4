import Test.Dogfood.Scenario.Atomic.DaemonIteration
import Test.Dogfood.Scenario.Atomic.RootFork

/-!
Concept: store-typing R4.
Consumer: the Atomic root native fork producer and its daemon role.
The actual daemon source point retains the initializer's three captured cells.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.DaemonGraph
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- The real first root fork enters exactly the checked daemon loop. -/
theorem root_child (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (point : Point) (held : RootGraph.PointAt built.program world point)
    (binder : point.env.length = 3) :
    CodeAt built.program built.table (resolve built.program (((point.child 0).child 0).child 0)) := by
  apply CodeAt.entry
  refine ⟨?_, binder, RootGraph.cells point held.2.1 held.2.2.1⟩
  have path : (((point.child 0).child 0).child 0).path = StageSource.bodyPath 0 := by
    change point.path ++ [0] ++ [0] ++ [0] = StageSource.bodyPath 0
    rw [held.2.1.2, binder]
    rfl
  rw [path]
  exact DaemonSource.source_at built accepted
end Test.Dogfood.Scenario.Atomic.DaemonGraph
