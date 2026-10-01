
namespace Test.Program.H2LookupDiagnostic
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def natKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def readService : NativeEff := .service natKey

theorem unit_is_not_context : Val.context? .unit = none := rfl

theorem missing_context_returns_badName :
    serviceLookupR natKey .unit = .pure (.failure (Cause.die .badName)) := rfl

theorem old_service_premise_vacuous (w : W) :
    ∀ ctx, Val.context? .unit = some ctx → ServicesFit w ctx.services := by
  intro ctx lookup
  rw [unit_is_not_context] at lookup
  cases lookup

/-- The exact old lookup_typed signature is false after the requested shared-exit strengthening.
This is a test-helper contract diagnostic, not a ninth production proof repair. -/
theorem old_lookup_statement_false (w : W) : ¬ (
    ∀ (ty : EffTy), ty.answer = .nat → ∀ v : Val,
      (∀ ctx, Val.context? v = some ctx → ServicesFit w ctx.services) →
      TypedProg readService w ty (serviceLookupR natKey v)) := by
  intro claimed
  have typed := claimed (EffTy.pure .nat) rfl .unit (old_service_premise_vacuous w)
  rw [missing_context_returns_badName] at typed
  exact Test.Program.H2PartOne.bad_current_code_refused readService w _ typed

/-- Proposed test-only amendment: demand that the input actually decodes as a context.
Do not replace the existing helper without reporting its changed premise. -/
theorem proposed_lookup_typed (w : W) (ty : EffTy) (answer : ty.answer = .nat) (v : Val)
    (isContext : ∃ ctx, Val.context? v = some ctx)
    (typed : ∀ ctx, Val.context? v = some ctx → ServicesFit w ctx.services)
    (keyType : nativeServiceTy natKey = some .nat) :
    TypedProg readService w ty (serviceLookupR natKey v) := by
  obtain ⟨ctx, hctx⟩ := isContext
  unfold serviceLookupR
  rw [hctx]
  split
  · rename_i value found
    have hfit := flatFits_fits (typed ctx hctx natKey value .nat found keyType)
    apply TypedProg.pure
    apply strongExit_success
    rw [answer]
    exact hfit
  · exact TypedProg.pure (Test.Program.H2PartOne.missingService_admitted_at_any_type w ty)

#print axioms unit_is_not_context
#print axioms missing_context_returns_badName
#print axioms old_service_premise_vacuous
#print axioms old_lookup_statement_false
#print axioms proposed_lookup_typed
end Test.Program.H2LookupDiagnostic
