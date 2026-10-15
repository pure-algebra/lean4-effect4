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

/-- The actual protected source finalizer always installs its real program before a pure arm. -/
theorem guarded_exit_edge (root : NativeEff) (table : RowTable) (owner : Nat)
    (world : StageWorld.World) (body : NCode) (point : Point)
    (callback : ∀ nextWorld, Future world nextWorld → ∀ view exit,
      StageFinalizer.BodyExit nextWorld owner exit →
      CodeAt root table owner nextWorld (FinalizerKind owner exit)
        (resolve root (({point with completed := view} : Point).childWith 1 (reifyExitVal exit)))) :
    Edge root table owner world (.body owner) (.finalized owner) (.onExit body (.fin point) false) := by
  apply EmbeddedEdgeOver.saved
  refine ⟨?_, ?_, ?_⟩
  · intro view
    refine SavedAt.mk world (StageWorld.Kind.body owner) (StageWorld.Kind.finalized owner) _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro nextWorld future value good absent
      cases absent
    · intro nextWorld future cause good absent
      cases absent
    · intro nextWorld future value provided next pushed good supplied noProgram actual
      change some _ = none at noProgram
      cases noProgram
    · intro nextWorld future cause provided next pushed good supplied noProgram actual
      change some _ = none at noProgram
      cases noProgram
    · intro nextWorld future exit next good installed
      change some (finalizerCode (interpAt root view table) exit
        (resolve root (({point with completed := view} : Point).childWith 1 (reifyExitVal exit)))) = some next at installed
      cases installed
      have captured : StageFinalizer.BodyExit nextWorld owner exit := by
        cases exit <;> exact good
      exact finalizer_code root table owner view nextWorld exit _ captured (callback nextWorld future view exit captured)
    · intro nextWorld future fiber cause delivered good arm interrupted skipped
      rw [ensure_protected_not_interrupted] at interrupted
      cases interrupted
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal

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
  | pause owns => exact .inl (.yieldNowWith _ (.pause owns))
  | pausing owns held =>
    exact .inl (.onSuccessConst _ _ _ (.pause owns) (pause_edge root table owner world _ _ _ owns held))
  | frontier zero =>
    apply Or.inl
    apply HeadAt.suspend
    change CodeAt root table owner world kind (suspendBodyAt root (.body _))
    simp only [suspendBodyAt, zero]
    exact .frontier rfl
  | suspended next => exact .inl (.suspend _ (next view))
  | guardedExit first callback =>
    apply Or.inl
    apply HeadAt.onExit (middle := StageWorld.Kind.body owner)
    · exact first
    · exact guarded_exit_edge root table owner world _ _ callback
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
