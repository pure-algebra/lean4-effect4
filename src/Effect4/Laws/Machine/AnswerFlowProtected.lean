import Effect4.Laws.Machine.AnswerFlowHooks

/-!
Concepts: scope-lifetime-finalization R11 and store-typing R4.
Question: protected native finalizers retain their actual installed result class.
Consumers: Timeout's numeric phase finalizers and initialized crew finalizer families.
Reach: every permitted future world and classed exit, with a total installed finalizer.
Limit: this rule supplies no finalizer program, input exit class, command producer, or progress.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
universe u v w
open Effect4
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {World Kind : Type w}
variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interp : PrimInterp ν σ β ε δ ι α)

/-- A total installed protected finalizer needs no arbitrary-cause discard premise.
The actual mask hook makes that discarded-handler branch impossible. -/
theorem saved_protected_finalizer (world : World) (input output : Kind)
    (body : Prim ν σ β ε δ ι α) (name : ν)
    (installed : ∀ nextWorld, model.future world nextWorld → ∀ exit,
      ExitAt model nextWorld input exit → ∃ next,
        model.finalizer nextWorld name exit = some next ∧ model.code nextWorld output next) :
    SavedAt model interp world input output (.onExit body name false) := by
  refine .mk world input output _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ absent
    cases absent
  · intro _ _ _ _ absent
    cases absent
  · intro nextWorld future value provided next pushed good supplied absent arm
    have exitGood : ExitAt model nextWorld input (provided.getD (.success value)) := by
      cases provided with
      | none => exact good
      | some exit => exact supplied exit rfl
    obtain ⟨code, present, _⟩ := installed nextWorld future _ exitGood
    change model.finalizer nextWorld name (provided.getD (.success value)) = none at absent
    rw [present] at absent
    cases absent
  · intro nextWorld future cause provided next pushed good supplied absent arm
    have exitGood : ExitAt model nextWorld input (provided.getD (.failure cause)) := by
      cases provided with
      | none => exact good
      | some exit => exact supplied exit rfl
    obtain ⟨code, present, _⟩ := installed nextWorld future _ exitGood
    change model.finalizer nextWorld name (provided.getD (.failure cause)) = none at absent
    rw [present] at absent
    cases absent
  · intro nextWorld future exit next good present
    obtain ⟨code, installedCode, typed⟩ := installed nextWorld future exit good
    change model.finalizer nextWorld name exit = some next at present
    have equal := Option.some.inj (installedCode.symm.trans present)
    rw [← equal]
    exact typed
  · intro nextWorld future fiber cause delivered good arm interrupted skipped
    rw [ensure_protected_not_interrupted] at interrupted
    cases interrupted

end Effect4.Machine.AnswerFlow
