import Effect4.Laws.Program.Typed.Contracts

/-!
E4-SCHED-CE-006/007: counterexamples to the 2026-09-21 input audit's proposed
delivery contract. These are exact evaluator equations on saved states, not a claim
that a complete decision tape reaches those states. They refute the proposed universal
stack statement, whose hypotheses do not require a reachable history.
-/
set_option autoImplicit false
namespace Test.Counterexamples.InterruptDelivery
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Program.Typed.Contracts
abbrev TWorld := Effect4.Program.Typed.World

def beforeCatch : EffTy := ⟨.nat, .nat, Effect4.Machine.Env.Requirement.empty⟩
def afterCatch : EffTy := EffTy.pure .nat
def failure : ExitV := .failure (Cause.fail (.tag 42))
def recovery (_ex : ExitV) : RProgram := .pure (.success (.nat 0))
def masked : RSaved :=
  ⟨.pure failure, [.restoreMask true, .resume .onFailure recovery], false,
    some (Cause.interrupt (some ⟨1⟩)), false⟩

/-- The audit's `ex.cause` is not a projection on Exit. This well-typed version states
its intended condition for every failure cause; our counterexample is a failure. -/
def ReviewedDeliveryStateOk (frame : RSaved) (ex : ExitV) : Prop :=
  frame.interruptible = true → frame.interruptedCause.isSome = true →
    frame.deferredInterrupt = true ∨
      ∀ cause, ex = .failure cause → ∀ reason ∈ cause.reasons, reason.tag = .interrupt

theorem masked_satisfies_reviewed_correlation : ReviewedDeliveryStateOk masked failure := by
  intro h
  exact Bool.noConfusion h

theorem masked_has_provenance : InterruptProvenance masked := by
  constructor
  · intro cause h reason mem
    change some (Cause.interrupt (some ⟨1⟩)) = some cause at h
    cases h
    change reason ∈ [Reason.interrupt (some ⟨1⟩) ReasonAnnotations.empty] at mem
    simp only [List.mem_singleton] at mem
    subst reason
    rfl
  · intro h
    exact Bool.noConfusion h

theorem original_failure_fits_input (w : TWorld) : ExitFits w beforeCatch failure := rfl

/-- The proposed guard-miss-only skip premise admits exactly this ordinary catch.
Together with restoreMask's identity arrow and the empty tail, its proposed stack
composition has input beforeCatch and output afterCatch. -/
theorem reviewed_catch_skip (w : TWorld) (ex : ExitV) (typed : ExitFits w beforeCatch ex)
    (miss : GuardKind.onFailure.hasExitArm ex = false) : ExitFits w afterCatch ex := by
  cases ex with
  | success value => exact typed
  | failure cause => cases miss

/-- The handler itself returns a well-typed pure value. The failure is in delivery,
not in the handler's result or the ordinary skip premise. -/
theorem reviewed_catch_run (w : TWorld) (ex : ExitV) :
    ∃ result, recovery ex = .pure result ∧ ExitFits w afterCatch result :=
  ⟨.success (.nat 0), rfl, rfl⟩

/-- Restoring the mask inside popR makes the catch skip, even though the entry mask
was false and the audit's correlation held at entry. -/
theorem restore_then_skip (interp : RInterp) :
    (popR interp failure masked.stack masked).2 = some failure := rfl

/-- Even the coarse consequence of the proposed StrongExit conclusion is false. Any
StrongExit that retains CompletionOk is therefore unable to establish that conclusion. -/
theorem proposed_entry_mask_exception_false (w : TWorld) :
    ¬ (ExitFits w afterCatch failure ∨
      (masked.interruptible = true ∧ masked.interruptedCause.isSome = true)) := by
  intro h
  cases h with
  | inl fits => exact Bool.noConfusion fits
  | inr flags => exact Bool.noConfusion flags.1

/-- Setting deferredInterrupt does not repair the failing-exit branch: deliverR only
intercepts successes. This is a second, independent defect in the proposed argument. -/
def deferred : RSaved := { masked with
  interruptible := true
  deferredInterrupt := true
  stack := [.resume .onFailure recovery] }

theorem deferred_satisfies_reviewed_correlation : ReviewedDeliveryStateOk deferred failure :=
  fun _ _ => Or.inl rfl

theorem delivery_does_not_intercept_failure (interp : RInterp) (m : RState) (f : RFiber)
    (yielding : Bool) :
    (deliverR interp m { f with frame := deferred } yielding failure).outcome = .finished failure := rfl

#print axioms masked_satisfies_reviewed_correlation
#print axioms masked_has_provenance
#print axioms reviewed_catch_skip
#print axioms reviewed_catch_run
#print axioms restore_then_skip
#print axioms proposed_entry_mask_exception_false
#print axioms delivery_does_not_intercept_failure
end Test.Counterexamples.InterruptDelivery
