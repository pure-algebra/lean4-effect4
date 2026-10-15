import Effect4.Laws.Machine.AnswerFlowFrames
import Effect4.Laws.Machine.AnswerFlowFamily

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual crew handlers and finalizers share saved-frame construction laws.
Reach: arbitrary answer classes, future worlds and the installed finalizer program.
Limit: recursive loop edges require an external SavedFamily.
Consumer: AnswerSlots.Typed native head and initialized crew answer flow.
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

/-- Both native result arms invoke their actual class-aware callbacks. -/
theorem saved_both (world : World) (input output : Kind)
    (body : Prim ν σ β ε δ ι α) (success failure : ν)
    (answer : ∀ nextWorld, model.future world nextWorld → ∀ value,
      model.value nextWorld input value → model.code nextWorld output (interp.contA success value))
    (cause : ∀ nextWorld, model.future world nextWorld → ∀ reason,
      model.cause nextWorld input reason → model.code nextWorld output (interp.contE failure reason))
    (discard : ∀ nextWorld, model.future world nextWorld → ∀ reason,
      model.cause nextWorld output reason) :
    SavedAt model interp world input output (.onSuccessAndFailure body success failure) := by
  refine .mk world input output _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ absent; cases absent
  · intro _ _ _ _ absent; cases absent
  · intro nextWorld future value provided next pushed good supplied absent arm
    change some (interp.contA success value, []) = some (next, pushed) at arm
    cases arm
    exact .mk nextWorld output output _ [] (answer nextWorld future value good) (.nil nextWorld output)
  · intro nextWorld future reason provided next pushed good supplied absent arm
    change some (interp.contE failure reason, []) = some (next, pushed) at arm
    cases arm
    exact .mk nextWorld output output _ [] (cause nextWorld future reason good) (.nil nextWorld output)
  · intro _ _ _ _ _ program; cases program
  · intro nextWorld future fiber reason delivered good selected interrupted skipped
    exact discard nextWorld future delivered

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Reifying a provided or current exit uses the input class of that actual exit. -/
theorem exit_getD (world : World) (input : Kind) (provided : Option (Exit β ε δ ι α))
    (fallback : Exit β ε δ ι α) (good : ExitAt model world input fallback)
    (supplied : ∀ exit ∈ provided, ExitAt model world input exit) :
    ExitAt model world input (provided.getD fallback) := by
  cases provided with
  | none => exact good
  | some exit => exact supplied exit rfl

/-- The native exit frame reifies exactly the actual delivered exit. -/
theorem saved_exitFrame (world : World) (input output : Kind) (body : Prim ν σ β ε δ ι α)
    (reify : ∀ nextWorld, model.future world nextWorld → ∀ exit,
      ExitAt model nextWorld input exit → model.value nextWorld output (interp.reifyExit exit))
    (discard : ∀ nextWorld, model.future world nextWorld → ∀ reason,
      model.cause nextWorld output reason) :
    SavedAt model interp world input output (.exitFrame body) := by
  refine .mk world input output _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ absent; cases absent
  · intro _ _ _ _ absent; cases absent
  · intro nextWorld future value provided next pushed good supplied absent arm
    change some (.success (interp.reifyExit (provided.getD (.success value))), []) = some (next, pushed) at arm
    cases arm
    exact .mk nextWorld output output _ []
      (model.success nextWorld output _ (reify nextWorld future _ (exit_getD model nextWorld input provided _ good supplied)))
      (.nil nextWorld output)
  · intro nextWorld future reason provided next pushed good supplied absent arm
    change some (.success (interp.reifyExit (provided.getD (.failure reason))), []) = some (next, pushed) at arm
    cases arm
    exact .mk nextWorld output output _ []
      (model.success nextWorld output _ (reify nextWorld future _ (exit_getD model nextWorld input provided _ good supplied)))
      (.nil nextWorld output)
  · intro _ _ _ _ _ program; cases program
  · intro nextWorld future fiber reason delivered good selected interrupted skipped
    exact discard nextWorld future delivered

/-- The native onExit frame uses installed finalizer code before its pure callback arm. -/
theorem saved_onExit (world : World) (input output : Kind)
    (body : Prim ν σ β ε δ ι α) (name : ν) (flag : Bool)
    (pure : ∀ nextWorld, model.future world nextWorld → ∀ exit,
      ExitAt model nextWorld input exit → model.finalizer nextWorld name exit = none →
      model.code nextWorld output (Prim.ofExit
        (Exit.restoreAfterFinalizer exit (interp.finalizerExit name exit))))
    (installed : ∀ nextWorld, model.future world nextWorld → ∀ exit next,
      ExitAt model nextWorld input exit → model.finalizer nextWorld name exit = some next →
      model.code nextWorld output next)
    (discard : ∀ nextWorld, model.future world nextWorld → ∀ reason,
      model.cause nextWorld output reason) :
    SavedAt model interp world input output (.onExit body name flag) := by
  refine .mk world input output _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ absent; cases absent
  · intro _ _ _ _ absent; cases absent
  · intro nextWorld future value provided next pushed good supplied absent arm
    change some (Prim.ofExit (Exit.restoreAfterFinalizer (provided.getD (.success value))
      (interp.finalizerExit name (provided.getD (.success value)))), []) = some (next, pushed) at arm
    cases arm
    exact .mk nextWorld output output _ []
      (pure nextWorld future _ (exit_getD model nextWorld input provided _ good supplied) absent)
      (.nil nextWorld output)
  · intro nextWorld future reason provided next pushed good supplied absent arm
    change some (Prim.ofExit (Exit.restoreAfterFinalizer (provided.getD (.failure reason))
      (interp.finalizerExit name (provided.getD (.failure reason)))), []) = some (next, pushed) at arm
    cases arm
    exact .mk nextWorld output output _ []
      (pure nextWorld future _ (exit_getD model nextWorld input provided _ good supplied) absent)
      (.nil nextWorld output)
  · intro nextWorld future exit next good program
    exact installed nextWorld future exit next good program
  · intro nextWorld future fiber reason delivered good selected interrupted skipped
    exact discard nextWorld future delivered
end Effect4.Machine.AnswerFlow
