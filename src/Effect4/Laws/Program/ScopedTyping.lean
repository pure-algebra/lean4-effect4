import Effect4.Program.Typing

/-!
# Scoped typing — exact service-requirement discharge (DI-63)

The statements concern the typing function, not resource execution or host cleanup.
Effect.scoped excludes Scope at vendor/effect-4.0.0-rc.112/src/Effect.ts:12815-12817.
The existing bodyRequires/Row algebra removes that one complete service key; the
successful answer/error fields and the body's refusal are retained. The native and
same-service-code/different-name controls are in Test/Program/ScopedTypingContract.lean.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine.Env

variable {Op : Type}

/-- DI-63: the full typing equation, including refused bodies. -/
theorem effTy_scoped (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    effTy sig env (.scoped body) =
      (effTy sig env body).map (fun t => { t with requires := bodyRequires sig t }) := rfl

/-- Scoping retains exactly A/E and removes only the signature's Scope requirement. -/
theorem effTy_scoped_some (sig : Signature Op) (env : TyEnv) (body : Eff Op)
    {t : EffTy} (h : effTy sig env body = some t) :
    effTy sig env (.scoped body) =
      some { t with requires := bodyRequires sig t } := by
  rw [effTy_scoped, h]
  rfl

/-- A scope never turns an ill-typed body into an admitted body, or conversely. -/
theorem effTy_scoped_none_iff (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    effTy sig env (.scoped body) = none ↔ effTy sig env body = none := by
  rw [effTy_scoped]
  cases effTy sig env body <;> simp

/-- The wrapper's admitted/refused flag agrees exactly with its body. -/
theorem effTy_scoped_isSome (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    (effTy sig env (.scoped body)).isSome = (effTy sig env body).isSome := by
  rw [effTy_scoped]
  cases effTy sig env body <;> rfl

/-- The exact Scope key does not remain in the discharged row. -/
theorem bodyRequires_not_scope (sig : Signature Op) (t : EffTy) :
    sig.scopeKey ∉ bodyRequires sig t := by
  simp [bodyRequires, Requirement.single, Row.mem_diff, Row.mem_singleton]

/-- Full-key comparison: every different key is retained iff the body required it. -/
theorem bodyRequires_other (sig : Signature Op) (t : EffTy) (key : ServiceKey)
    (different : key ≠ sig.scopeKey) :
    key ∈ bodyRequires sig t ↔ key ∈ t.requires := by
  simp [bodyRequires, Requirement.single, Row.mem_diff, Row.mem_singleton, different]

/-- The existing canonical row difference makes the discharge idempotent. -/
theorem bodyRequires_idempotent (sig : Signature Op) (t : EffTy) :
    bodyRequires sig { t with requires := bodyRequires sig t } = bodyRequires sig t :=
  Row.diff_single_twice t.requires sig.scopeKey

/-- Nested scopes have exactly the inner scope's typing result, including refusal. -/
theorem effTy_scoped_idempotent (sig : Signature Op) (env : TyEnv) (body : Eff Op) :
    effTy sig env (.scoped (.scoped body)) = effTy sig env (.scoped body) := by
  simp only [effTy_scoped]
  cases h : effTy sig env body with
  | none => rfl
  | some t => simp only [Option.map_some, bodyRequires, Row.diff_single_twice]

end Effect4.Program
