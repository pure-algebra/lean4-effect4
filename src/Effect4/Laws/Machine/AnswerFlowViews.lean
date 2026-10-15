import Effect4.Laws.Machine.AnswerFlowFamily
import Effect4.Laws.Machine.MaskRuns

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: saved callbacks retain their answer classes when the completed-fiber view changes.
Reach: one common saved frame and kind endpoints, with every interpreter view certified.
Limit: recursive loop and iterator hooks use their own source-name classes.
Consumer: the typed stable graph and initialized native history producer.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
open Effect4 Effect4.Contracts
universe u v w t
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w} {View : Type t}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable (models : View → Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interps : View → PrimInterp ν σ β ε δ ι α)

/-- A nonrecursive saved frame retains the same input and output classes at every actual view. -/
structure ViewSavedAt (world : World) (input output : Kind) (frame : Prim ν σ β ε δ ι α) : Prop where
  each : ∀ view, SavedAt (models view) (interps view) world input output frame
  noLoop : ∀ name cursor, frame ≠ .whileLoop name cursor
  noIterator : ∀ name cursor, frame ≠ .iterator name cursor

/-- A nonrecursive value arm pushes no frames, so its actual suffix is uniform across views. -/
theorem nonrecursive_armA_nil (interp : PrimInterp ν σ β ε δ ι α) (frame : Prim ν σ β ε δ ι α)
    (noLoop : ∀ name cursor, frame ≠ .whileLoop name cursor)
    (noIterator : ∀ name cursor, frame ≠ .iterator name cursor)
    (value : β) (provided : Option (Exit β ε δ ι α)) (next : Prim ν σ β ε δ ι α)
    (pushed : List (Prim ν σ β ε δ ι α))
    (actual : frame.armA interp value provided = some (next, pushed)) : pushed = [] := by
  cases frame
  case whileLoop name cursor => exact (noLoop name cursor rfl).elim
  case iterator name cursor => exact (noIterator name cursor rfl).elim
  all_goals cases actual <;> rfl

/-- A uniform saved certificate retains every future-view semantic witness. -/
theorem ViewSavedAt.future {first last : World}
    (future : ∀ view, (models view).future first last) {input output : Kind}
    {frame : Prim ν σ β ε δ ι α} (held : ViewSavedAt models interps first input output frame) :
    ViewSavedAt models interps last input output frame :=
  ⟨fun view => saved_mono (models view) (interps view) (future view) (held.each view), held.noLoop, held.noIterator⟩

/-- The actual interpreter view reads one family while retaining a uniform actual pushed suffix. -/
theorem ViewSavedAt.family (view : View) :
    SavedFamily (models view) (interps view) (ViewSavedAt models interps) := by
  have single := saved_family (models view) (interps view)
  constructor
  · intro world input output frame held
    exact single.skip world input output frame (held.each view)
  · intro world input output frame held
    exact single.skipCause world input output frame (held.each view)
  · intro world input output frame held nextWorld future value provided next pushed good supplied absent actual
    have empty := nonrecursive_armA_nil (interps view) frame held.noLoop held.noIterator value provided next pushed actual
    subst pushed
    obtain ⟨middle, code, path⟩ := single.answer world input output frame (held.each view)
      nextWorld future value provided next [] good supplied absent actual
    cases path
    exact ⟨output, code, .nil output⟩
  · intro world input output frame held nextWorld future cause provided next pushed good supplied absent actual
    have empty := FrameFiber.armE_pushes_nothing (interps view) frame cause provided next pushed actual
    subst pushed
    obtain ⟨middle, code, path⟩ := single.cause world input output frame (held.each view)
      nextWorld future cause provided next [] good supplied absent actual
    cases path
    exact ⟨output, code, .nil output⟩
  · intro world input output frame held
    exact single.program world input output frame (held.each view)
  · intro world input output frame held
    exact single.discard world input output frame (held.each view)
end Effect4.Machine.AnswerFlow
