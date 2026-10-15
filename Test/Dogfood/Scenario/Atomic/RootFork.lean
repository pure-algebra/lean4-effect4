import Test.Dogfood.Scenario.Atomic.RootFrame
import Test.Dogfood.Scenario.Atomic.StageEntry

/-!
Concept: store-typing R4.
Consumer: the actual Atomic root native fork transition and its child-role assignment.
The returned handle and the new request frame share the same advanced stage world.
No history or cancellation authority follows from this local source transition.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Allocating a child changes no heap field or request stage. -/
theorem allocate_heap (world : StageWorld.World) (state : Stores) (held : HeapAt world state) :
    HeapAt (allocate world) state := by
  obtain ⟨witness⟩ := held
  exact ⟨witness⟩

/-- The actual fork answer advances the root's captured handle class at the same new counter. -/
theorem fork_answer (root : NativeEff) (world : StageWorld.World) (point : Point) (id : Nat)
    (small : id < 7) (held : PointAt root world point)
    (binder : point.env.length = StageSource.forkBinder id) :
    ValueAt (allocate world) (.rootAnswer point.env.length) (.fiber ⟨id + 1⟩) := by
  refine ⟨?_, RootBindings.fork_answer point.env id small binder⟩
  change world.nextId + 1 = RootSlots.rank (point.env.length + 1)
  rw [held.2.2.2.2, binder, (RootBindings.fork_rank id small).1, (RootBindings.fork_rank id small).2]

/-- A real request fork enters its actual protected body with the still-waiting request stage. -/
theorem request_child (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (fresh : Fresh world) (point : Point) (id : Nat) (member : id ∈ requests)
    (body rest : NativeEff) (options : Supervision.ForkOptions)
    (held : PointAt built.program world point) (binder : point.env.length = StageSource.forkBinder id)
    (found : Node.at_ (.eff built.program) point.path = some (.eff (.bind (.withFiber (.fork body options)) rest))) :
    StageGraph.CodeAt built.program built.table id (allocate world) (.finalized id)
      (resolve built.program (((point.child 0).child 0).child 0)) := by
  have small : id < 7 := by
    simp only [requests, List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  have counter : world.nextId = id + 1 := by
    rw [held.2.2.2.2, binder]
    exact (RootBindings.fork_rank id small).1
  apply StageEntry.request_code built accepted id member
  · change (point.path ++ [0]) ++ [0] ++ [0] = SourcePaths.requestPath id
    rw [held.2.1.2, binder, ← StageSource.request_body_path id member]
    simp only [StageSource.bodyPath, StageSource.forkPath, List.append_assoc, List.cons_append, List.nil_append]
  · exact fork_child_scope built.program world point body rest options held found
  · exact cells point held.2.1 held.2.2.1
  · exact (new_request world fresh id member counter).1
end Test.Dogfood.Scenario.Atomic.RootGraph
