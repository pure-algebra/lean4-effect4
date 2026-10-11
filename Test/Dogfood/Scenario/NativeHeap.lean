import Test.Dogfood.Scenario.SourceFragment
import Test.Dogfood.Scenario.Atomic.Store
import Effect4.Laws.Program.HeapSites

/-!
# Actual cell readers after native histories

Concept: store-typing R4, serving `Atomic.bounded` and the Queue cell premise.
These readers use the actual sources and every control history.
The Atomic reader consumes its proved write-site census.
The Queue reader retains the predicate's write-site premise and every natural job count.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.NativeHeap
open Effect4 Effect4.Program Effect4.Store

/-- Every actual shop cell retains the proved `used` bound after any control history. -/
theorem shop_cell (b : Api.Built) (built : Api.Author.build (Atomic.shop .none) = .ok b)
    (compileFuel : Nat) (m : NativeMachine) (history : Run.ControlHistory b compileFuel m)
    (index : Nat) (value : Val) (found : m.state.refs[index]? = some value) :
    Atomic.Store.UsedOk value :=
  (HeapSites.heap_sites_keep b compileFuel Atomic.Store.UsedOk
    (SourceFragment.atomic_built_fragment b built)
    (Atomic.Store.shop_sites_used b built) m history) index value found

/-- Every actual queue cell retains its write-site predicate at every job count. -/
theorem queue_cell (total compileFuel : Nat) (b : Api.Built)
    (built : Api.Author.build (QueueWorkers.crew total) = .ok b) (P : Val → Prop)
    (sites : HeapSites.SitesKeep b.program P) (m : NativeMachine)
    (history : Run.ControlHistory b compileFuel m) (index : Nat) (value : Val)
    (found : m.state.refs[index]? = some value) : P value :=
  (SourceFragment.queue_heap_at total compileFuel b built P sites m history) index value found

end Test.Dogfood.Scenario.NativeHeap
