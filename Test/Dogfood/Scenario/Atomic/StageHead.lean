import Test.Dogfood.Scenario.Atomic.StageGraph
import Effect4.Laws.Machine.AnswerFlowHead

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the actual request native producer for `Atomic.Store.shop_stages`.
Current source annotations expose the existing frame head or its stateful operation.
Finalizer restore and merge edges reuse their checked contextual family.
No new primitive-code or source traversal occurs here.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Every annotated request head is an ordinary frame step or its actual stateful operation. -/
theorem head_or_sync (root : NativeEff) (table : RowTable) (owner : Nat)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (kind : StageWorld.Kind)
    (code : NCode) (owned : CodeAt root table owner world kind code) :
    HeadAt (model root table owner view) (interpAt root view table).toPrimInterp
      (Edge root table owner) world kind code ∨ ∃ operation, code = .sync (.op operation) := by
  cases owned with
  | success good => exact .inl (.success _ good)
  | failure good => exact .inl (.failure _ good)
  | decision => exact .inr ⟨_, rfl⟩
  | deposit => exact .inr ⟨_, rfl⟩
  | reading => exact .inr ⟨_, rfl⟩
  | note => exact .inr ⟨_, rfl⟩
  | yielding waiting => exact .inl (.yieldNowWith _ (.yielding waiting))
  | frontier zero =>
    apply Or.inl
    apply HeadAt.suspend
    change CodeAt root table owner world kind (suspendBodyAt root (.body _))
    simp only [suspendBodyAt, zero]
    exact .frontier rfl
  | suspended next => exact .inl (.suspend _ (next view))
  | restoring captured first =>
    apply Or.inl
    apply HeadAt.onSuccess (middle := StageWorld.Kind.cleanup owner)
    · exact first
    · exact EmbeddedEdgeOver.mapped trivial (StageFinalizer.Edge.restore world owner _ _ captured)
  | merging captured first =>
    apply Or.inl
    apply HeadAt.onFailure (middle := StageWorld.Kind.note owner)
    · exact first
    · exact EmbeddedEdgeOver.mapped trivial (StageFinalizer.Edge.merge world owner _ _ captured)
  | bound localInput first callback skip =>
    exact .inl (.onSuccess _ _ _ first (bound_edge root table owner world _ _ _ _ callback skip))
end Test.Dogfood.Scenario.Atomic.StageGraph
