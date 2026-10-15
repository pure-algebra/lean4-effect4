import Effect4.Laws.Machine.AnswerFlowViews

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: native scope callbacks retain their source-generated endpoint annotation beside uniform semantic edges.
Reach: any refinement of a uniform nonrecursive saved certificate, with the same actual empty pushed suffix.
Limit: the refinement must be constructed at each actual edge introduction.
Consumer: crew scoped-exit tags and initialized native evaluator preservation.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
open Effect4 Effect4.Contracts
universe u v w t
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w} {View : Type t}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- A generated annotation refines the uniform family without another callback or pop induction. -/
theorem ViewSavedAt.refined_family
    (models : View → Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (interps : View → PrimInterp ν σ β ε δ ι α)
    (Certificate : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (read : ∀ world input output frame, Certificate world input output frame →
      ViewSavedAt models interps world input output frame) (view : View) :
    SavedFamily (models view) (interps view) Certificate := by
  have base := ViewSavedAt.family models interps view
  constructor
  · intro world input output frame held
    exact base.skip world input output frame (read world input output frame held)
  · intro world input output frame held
    exact base.skipCause world input output frame (read world input output frame held)
  · intro world input output frame held nextWorld future value provided next pushed good supplied absent actual
    have certificate := read world input output frame held
    have empty := nonrecursive_armA_nil (interps view) frame certificate.noLoop certificate.noIterator value provided next pushed actual
    subst pushed
    obtain ⟨middle, code, suffix⟩ := base.answer world input output frame certificate
      nextWorld future value provided next [] good supplied absent actual
    cases suffix
    exact ⟨output, code, .nil output⟩
  · intro world input output frame held nextWorld future cause provided next pushed good supplied absent actual
    have empty := FrameFiber.armE_pushes_nothing (interps view) frame cause provided next pushed actual
    subst pushed
    obtain ⟨middle, code, suffix⟩ := base.cause world input output frame (read world input output frame held)
      nextWorld future cause provided next [] good supplied absent actual
    cases suffix
    exact ⟨output, code, .nil output⟩
  · intro world input output frame held
    exact base.program world input output frame (read world input output frame held)
  · intro world input output frame held
    exact base.discard world input output frame (read world input output frame held)
end Effect4.Machine.AnswerFlow
