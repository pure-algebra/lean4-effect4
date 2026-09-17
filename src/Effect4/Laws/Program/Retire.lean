import Effect4.Program.Typing

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

end Effect4.Program
