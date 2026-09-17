import Effect4.Program.Typing
import Effect4.Laws.Program.Invocation

/-!
# Laws.Program.Retire — a retiring constructor's rewrite keeps every typing

The `Eff` series (DI-79) retires constructors into `select` and `iterate`. Before a constructor
is deleted, its rewrite is proved to keep the checker's answer. The deletion commit removes
that constructor's half of this module together with the constructor, since neither can be
stated without it; the record is the proof having been checked, and the commit that held it.

`branch` retired into `select … .bool`. Its half (`retireBranch`, the identity fold with one
slot replaced; `effTy_retireBranch`, the checker's whole answer kept at every sort and in every
environment, refusals included; `effTy_select_bool` and `denote_select_bool`, the node's typing
and meaning equations) was checked at `438b93f2` and left with the constructor.

`whileLoop` retires into `iterate`. Its rewrite needs the cursor's type, so it is stated at a
node: `effTy_iterate_of_whileLoop`.

`yieldError` retired into `fail`, the failure it meant. Its half (`retireYieldError`,
`effTy_retireYieldError` over whole programs, `denote_yieldError` at a node) was checked at
`478ed4b7` and left with the constructor. The machine differed in one place only: it took one
step from a yieldable error to its failure, and takes none from `fail`.

`callback` retires into `perform`, the one invocation form, whose row kind selects the route
(the plan's §3.4). `effTy_perform_of_callback`: a typed `callback` is a typed `perform` at the
same type; the converse is false on purpose, since a `perform` on a synchronous row is typed and
a `callback` on it is not. `compileEff_perform_of_callback`: under the native signature a typed
`callback` compiles to exactly the code of the `perform` (DI-61's `compile_perform_eq_callback`
with its premise read off the typing).
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-- The loop's rewrite, `whileLoop i t s b ↦ iterate c i t s unit b` at `c`, the type of the
initial cursor: whatever type the checker gave the unit loop, it gives the rewritten one. The
converse does not hold and is not wanted: `iterate` admits a step whose type is under the
cursor's, where `whileLoop` asked for the cursor's type exactly, so the rewrite admits more
programs and never fewer. -/
theorem effTy_iterate_of_whileLoop (sig : Signature Op) (env : TyEnv) (initial test step : Term)
    (body : Eff Op) (ty : EffTy) (h : effTy sig env (.whileLoop initial test step body) = some ty) :
    ∃ cursor, termTy sig env initial = some cursor ∧
      effTy sig env (.iterate cursor initial test step (.lit .unit) body) = some ty := by
  simp only [effTy, Option.bind_eq_bind] at h
  cases hc : termTy sig env initial with
  | none => rw [hc] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
  | some cursor =>
    refine ⟨cursor, rfl, ?_⟩
    rw [hc] at h
    simp only [Option.bind_some] at h
    cases ht : termTy sig (env ++ [cursor]) test with
    | none => rw [ht] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
    | some t =>
      rw [ht] at h
      simp only [Option.bind_some] at h
      cases hb : effTy sig (env ++ [cursor]) body with
      | none => rw [hb] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
      | some b =>
        rw [hb] at h
        simp only [Option.bind_some] at h
        cases hs : termTy sig (env ++ [cursor, b.answer]) step with
        | none => rw [hs] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
        | some s =>
          rw [hs] at h
          simp only [Option.bind_some] at h
          split at h
          · next hcond =>
            obtain ⟨htb, hsc⟩ := hcond
            subst htb
            subst hsc
            simp only [effTy, Option.bind_eq_bind, hc, ht, hb, hs, Option.bind_some, termTy,
              Ty.sub_refl, and_self, if_true]
            exact h
          · exact absurd h nofun

/-! ## `callback` into `perform` -/

/-- One node: a typed `callback` is a typed `perform`, at the same type. -/
theorem effTy_perform_of_callback (sig : Signature Op) (env : TyEnv) (op : Op) (request : Term)
    (ty : EffTy) (h : effTy sig env (.callback op request) = some ty) :
    effTy sig env (.perform op request) = some ty := by
  simp only [effTy, Option.bind_eq_bind] at h ⊢
  cases hr : termTy sig env request with
  | none => rw [hr] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
  | some r =>
    rw [hr] at h
    simp only [Option.bind_some] at h ⊢
    split at h
    · next hcond =>
      rw [if_pos ⟨hcond.1, hcond.2.2⟩]
      exact h
    · exact absurd h nofun

/-- Under the native signature a typed `callback` and the `perform` it rewrites to compile to
the same code, at every point and fuel. -/
theorem compileEff_perform_of_callback (table : RowTable) (env : TyEnv) (op : NativeOp)
    (request : Term) (ty : EffTy)
    (h : effTy (nativeSignature table) env (.callback op request) = some ty) (p : Point) :
    compileEff (.perform op request) p = compileEff (.callback op request) p := by
  apply compile_perform_eq_callback
  simp only [effTy, Option.bind_eq_bind] at h
  cases hr : termTy (nativeSignature table) env request with
  | none => rw [hr] at h; exact absurd h (by simp only [Option.bind_none]; exact nofun)
  | some r =>
    rw [hr] at h
    simp only [Option.bind_some] at h
    split at h
    · next hcond =>
      have hkind := hcond.2.1
      cases op with
      | external i => exact .inl ⟨i, rfl⟩
      | _ => exact .inr (by simpa only [nativeSignature, nativeRowOf, Row.normalizeTypes] using hkind)
    · exact absurd h nofun

end Effect4.Program
