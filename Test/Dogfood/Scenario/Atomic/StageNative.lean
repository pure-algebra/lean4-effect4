import Test.Dogfood.Scenario.Atomic.StageHead
import Test.Dogfood.Scenario.Atomic.StageHeap

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the actual request native iteration for `Atomic.Store.shop_stages`.
The actual operation, returned answer, next heap and stage assignment share one witness.
Command queues and whole histories remain separate consumers.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageGraph
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Every real request sync operation advances its heap and answer in the same stage world. -/
theorem sync_heap (root : NativeEff) (table : RowTable) (owner : Nat) (member : owner ∈ requests)
    (world : StageWorld.World) (kind : StageWorld.Kind) (operation : SyncOp)
    (owned : CodeAt root table owner world kind (.sync (.op operation)))
    (state : Stores) (heap : HeapAt world state) :
    ∃ nextWorld after answer, syncOpStep operation state = some (after, answer) ∧
      Future world nextWorld ∧ RequestChange world nextWorld owner ∧ HeapAt nextWorld after ∧ ValueAt nextWorld kind answer := by
  cases owned with
  | decision waiting =>
    obtain ⟨after, next, answer, actual, future, locality, heapNext, good⟩ := decision_heap world owner member waiting state _ heap
    exact ⟨next, after, answer, actual, future, locality, heapNext, good⟩
  | deposit selected =>
    obtain ⟨after, answer, actual, future, locality, heapNext, good⟩ := deposit_heap world owner member selected state _ heap
    exact ⟨_, after, answer, actual, future, locality, heapNext, good⟩
  | reading =>
    obtain ⟨used, window, good⟩ := window_answer world state heap owner member
    refine ⟨world, state, _, ?_, order.refl world, request_change_refl world owner, heap, good⟩
    change (refStep (.refGet ⟨0⟩) state.refs).map (fun step => ({state with refs := step.2}, step.1)) = _
    simp only [refStep, window, Option.map_some]
  | note positive =>
    obtain ⟨after, actual, future, locality, heapNext, good⟩ := note_heap world owner state _ _ _ _ heap positive
    exact ⟨_, after, .unit, actual, future, locality, heapNext, good⟩
end Test.Dogfood.Scenario.Atomic.StageGraph
