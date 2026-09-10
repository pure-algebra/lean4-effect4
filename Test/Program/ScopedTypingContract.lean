import Effect4.Program.Native
import Effect4.Laws.Program.ScopedTyping

/-!
# DI-63 contract: exact scoped typing

Independent finite controls supplement the universal typing/row statements.
A same-service-code/different-name requirement must survive: removing by service code
would fail that control. No execution, finalization or host-equivalence claim is made here.
-/

set_option autoImplicit false

namespace Test.Program.ScopedTypingContract

open Effect4 Effect4.Program Effect4.Machine.Env

#check (@Effect4.Program.effTy_scoped :
  ∀ {Op : Type} (sig : Signature Op) (env : TyEnv) (body : Eff Op),
    effTy sig env (.scoped body) =
      (effTy sig env body).map (fun t => { t with requires := bodyRequires sig t }))

#check (@Effect4.Program.bodyRequires_other :
  ∀ {Op : Type} (sig : Signature Op) (t : EffTy) (key : ServiceKey),
    key ≠ sig.scopeKey → (key ∈ bodyRequires sig t ↔ key ∈ t.requires))

#check (@Effect4.Program.effTy_scoped_idempotent :
  ∀ {Op : Type} (sig : Signature Op) (env : TyEnv) (body : Eff Op),
    effTy sig env (.scoped (.scoped body)) = effTy sig env (.scoped body))

def acquisition : NativeEff :=
  .acquireRelease (.succeed (.lit (.nat 7))) (.succeed (.lit .unit))

def otherKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

def mixed : NativeEff := .bind acquisition (.service otherKey)

#guard typeOf nativeSignature acquisition =
  some ⟨.nat, .never, Requirement.single nativeScopeKey⟩
#guard typeOf nativeSignature (.scoped acquisition) = some (EffTy.pure .nat)
#guard typeOf nativeSignature (.scoped mixed) =
  some ⟨.nat, .never, Requirement.single otherKey⟩
#guard typeOf nativeSignature (.scoped (.scoped mixed)) =
  typeOf nativeSignature (.scoped mixed)
#guard typeOf nativeSignature (.scoped (.fail (.lit (.nat 9)))) =
  some ⟨.never, .nat, Requirement.empty⟩
#guard typeOf nativeSignature (.scoped (.succeed (.var 0))) = none
#guard typeOf nativeSignature (.scoped (.scoped (.succeed (.var 0)))) = none

/-- This fixture isolates requirement identity; no host service is executed. -/
def sameCodeOtherName : ServiceKey := ⟨⟨4⟩, nativeScopeKey.service⟩

def requirementRow : Row :=
  { name := "scopedRequirementControl", spelling := "Control.requirement", kind := .async,
    registration := .external, request := .unit, answer := .nat, error := .never,
    requires := [nativeScopeKey, sameCodeOtherName], cite := "" }

#guard sameCodeOtherName ≠ nativeScopeKey
#guard sameCodeOtherName.service = nativeScopeKey.service
#guard typeOf (nativeSignature [requirementRow])
    (.scoped (.callback (.external 0) (.lit .unit))) =
  some ⟨.nat, .never, Requirement.single sameCodeOtherName⟩

#print axioms Effect4.Program.effTy_scoped
#print axioms Effect4.Program.effTy_scoped_some
#print axioms Effect4.Program.effTy_scoped_none_iff
#print axioms Effect4.Program.effTy_scoped_isSome
#print axioms Effect4.Program.bodyRequires_not_scope
#print axioms Effect4.Program.bodyRequires_other
#print axioms Effect4.Program.bodyRequires_idempotent
#print axioms Effect4.Program.effTy_scoped_idempotent

end Test.Program.ScopedTypingContract
