import Effect4.Laws.Machine.AnswerFlowFamilyPop
import Effect4.Program.Compile

/-!
Reader: an actual failure callback family accepts interruption causes without typed failures.
Control: the same family cannot accept a fabricated typed pending failure.
The control bounds the saved-handler contract, not any source history.
-/
set_option autoImplicit false
namespace Test.Machine.AnswerFlowContextual
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow

private def Clean (cause : CauseV) : Prop :=
  ∀ reason ∈ cause.reasons, reason.tag ≠ .fail

private def model : Model (ν := EffName) (σ := EffThunk) (β := Val)
    (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) Unit Unit where
  future _ _ := True
  future_refl _ := trivial
  future_trans _ _ _ _ _ := trivial
  value _ _ _ := True
  cause _ _ := Clean
  code _ _ _ := True
  finalizer _ _ _ := none
  success _ _ _ _ := trivial
  failure _ _ _ _ := trivial

private def interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann :=
  (interpOf (.succeed (.lit .unit)) []).toPrimInterp

private def frame : NCode := .onFailure (.success .unit) .abort
private def Edge (_ : Unit) (_ _ : Unit) (code : NCode) : Prop := code = frame
private def Allowed (_ : Unit) (pending : Option CauseV) : Prop := ∀ cause ∈ pending, Clean cause

/-- Reader: the concrete catch frame uses the actual admitted recorded cause. -/
private theorem admitted_family : ContextualSavedFamily model interp Edge Allowed := by
  constructor
  · intros; trivial
  · intro world input output code held nextWorld future cause good missing
    subst code
    cases missing
  · intro world input output code held nextWorld future value provided next pushed good supplied absent arm
    subst code
    cases arm
  · intro world input output code held nextWorld future cause provided next pushed good supplied absent arm
    subst code
    change some (interp.contE .abort cause, []) = some (next, pushed) at arm
    cases arm
    cases output
    exact ⟨(), trivial, .nil ()⟩
  · intro world input output code held nextWorld future exit next good installed
    subst code
    cases installed
  · intro world input output code held nextWorld future fiber cause delivered good selected admitted interrupted actual
    subst code
    change Clean delivered
    cases pending : fiber.interruptedCause with
    | none =>
      simp only [frame, Prim.ensure, FrameFiber.skippedCause, pending] at actual
      cases actual
      exact good
    | some recorded =>
      have clean := admitted recorded pending
      simp only [frame, Prim.ensure, FrameFiber.skippedCause, pending] at actual
      cases actual
      exact Cause.sanitize_clean cause recorded clean

/-- Control: a typed failure fabricated as a recorded interrupt violates the unconditional family. -/
private theorem fabricated_pending_rejected : ¬ SavedFamily model interp Edge := by
  intro family
  let typed : CauseV := Cause.fail (.text "fabricated")
  let fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann :=
    ⟨.success .unit, [], true, some typed, false⟩
  have clean := family.discard () () () frame rfl () trivial fiber Cause.empty typed
    (by intro reason member; cases member) rfl rfl rfl
  exact clean (Reason.fail (.text "fabricated") ReasonAnnotations.empty) (by decide) rfl

end Test.Machine.AnswerFlowContextual
