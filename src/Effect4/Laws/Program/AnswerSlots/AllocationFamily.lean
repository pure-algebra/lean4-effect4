import Effect4.Laws.Program.AnswerSlots.AllocationProvenance

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual initializer saved edges retain their source point and exact heap until entry.
Reach: every interpreter view, actual returned allocation keys and actual pushed suffixes.
Consumer: the common bare initializer native producer and numeric entry hooks.
The family supplies no machine history or scheduler progress by itself.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts

/-- One actual allocation edge retains its origin through every permitted later world. -/
theorem semantic_future (spec : Spec) (before after : World) (future : Future before after)
    (input output : Kind spec.stable.Kind) (frame : NCode) (held : Semantic spec before input output frame) :
    Semantic spec after input output frame := by
  cases held with
  | saved saved scopeReady =>
    exact .saved (AnswerFlow.ViewSavedAt.future (fun view => model spec view)
      (fun view => (interpAt spec.root view spec.table).toPrimInterp) (fun _ => future) saved)
      (fun body previous scope flag same => ready_future spec before after future (scopeReady body previous scope flag same))
  | allocation captured index point body small stage reached =>
    exact .allocation captured index point body small stage ((model spec []).future_trans _ _ _ reached future)
  | gate captured point body stage gate present reached =>
    exact .gate captured point body stage gate present ((model spec []).future_trans _ _ _ reached future)

/-- Actual allocation and gate callback frames satisfy the existing shared saved-family contract. -/
theorem semantic_family (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) :
    AnswerFlow.SavedFamily (model spec view) (interpAt spec.root view spec.table).toPrimInterp (Semantic spec) := by
  have uniform := AnswerFlow.ViewSavedAt.family (fun view => model spec view)
    (fun view => (interpAt spec.root view spec.table).toPrimInterp) view
  constructor
  · intro world input output frame held nextWorld future value good missing
    cases held with
    | saved held scopeReady => exact uniform.skip world input output frame held nextWorld future value good missing
    | allocation => cases missing
    | gate => cases missing
  · intro world input output frame held nextWorld future cause good missing
    cases held with
    | saved held scopeReady => exact uniform.skipCause world input output frame held nextWorld future cause good missing
    | allocation => exact good
    | gate => exact good
  · intro world input output frame held nextWorld future value provided next pushed good supplied absent actual
    cases held with
    | saved held scopeReady =>
      have empty := AnswerFlow.nonrecursive_armA_nil (interpAt spec.root view spec.table).toPrimInterp
        frame held.noLoop held.noIterator value provided next pushed actual
      subst pushed
      obtain ⟨middle, code, path⟩ := uniform.answer world input output frame held nextWorld future value provided next [] good supplied absent actual
      cases path
      exact ⟨output, code, .nil output⟩
    | allocation captured index point body small stage reached =>
      change some ((interpAt spec.root view spec.table).contA (.cont point) value, []) = some (next, pushed) at actual
      cases actual
      exact ⟨.stable spec.stable.rootKind, allocation_callback spec fragment captured nextWorld index point small stage
        ((model spec view).future_trans _ _ _ reached future) view value good, .nil _⟩
    | gate captured point body stage gate present reached =>
      change some ((interpAt spec.root view spec.table).contA (.cont point) value, []) = some (next, pushed) at actual
      cases actual
      refine ⟨.stable spec.stable.rootKind, .entered fragment ?_, .nil _⟩
      exact gate_entry spec captured nextWorld point stage ((model spec view).future_trans _ _ _ reached future)
        gate present view value good
  · intro world input output frame held nextWorld future cause provided next pushed good supplied absent actual
    cases held with
    | saved held scopeReady =>
      have empty := FrameFiber.armE_pushes_nothing (interpAt spec.root view spec.table).toPrimInterp frame cause provided next pushed actual
      subst pushed
      obtain ⟨middle, code, path⟩ := uniform.cause world input output frame held nextWorld future cause provided next [] good supplied absent actual
      cases path
      exact ⟨output, code, .nil output⟩
    | allocation => cases actual
    | gate => cases actual
  · intro world input output frame held nextWorld future exit next good installed
    cases held with
    | saved held scopeReady => exact uniform.program world input output frame held nextWorld future exit next good installed
    | allocation => cases installed
    | gate => cases installed
  · intro world input output frame held nextWorld future fiber cause delivered good selected interrupted actual
    cases held with
    | saved held scopeReady => exact uniform.discard world input output frame held nextWorld future fiber cause delivered good selected interrupted actual
    | allocation => cases selected
    | gate => cases selected

/-- The structured initializer family and supplied stable family share one actual saved suffix. -/
theorem family (spec : Spec) (fragment : SourceScope.Fragment spec.root) (view : List (FiberId × ExitV)) :
    AnswerFlow.SavedFamily (model spec view) (interpAt spec.root view spec.table).toPrimInterp (Edge spec fragment) :=
  AnswerFlow.FamilyEmbedding.family_over (interpAt spec.root view spec.table).toPrimInterp
    (embedding spec view) (Semantic spec) (spec.laws fragment).Edge
    (semantic_family spec fragment view) ((spec.laws fragment).family view)

end Effect4.Program.AnswerSlots.AllocationAdapter
