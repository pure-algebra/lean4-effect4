import Effect4.Laws.Program.Typed
import Conform.Spec.Reflect

/-!
# Conform.Spec.Probe3 — the leaf specifications harvested, the generator called with no list

`harvest_specs effTy` reads the body of `effTy`, finds every `Option`-valued constant it applies,
and declares a `@[spec]` reflection specification for each. After that, `mvcgen` on an arm needs
no `[…]` list: the database already holds what the arm's leaves need. Two arms from `Probe1`
restated to show it, and the `.gen` arm (whose leaf `stmtsTy` nobody named by hand).
-/

namespace Conform.Spec.Probe3

open Std.Do
open Effect4.Program
open Conform.Spec

set_option linter.unusedVariables false

harvest_specs Effect4.Program.effTy

#check @Effect4.Program.effTy_reflect
#check @Effect4.Program.termTy_reflect

theorem effTy_bind_spec {Op : Type} (sig : Signature Op) (env : TyEnv) (first rest : Eff Op) :
    ⦃⌜True⌝⦄ effTy sig env (.bind first rest)
    ⦃(fun t => ⌜∃ f r, effTy sig env first = some f ∧
        effTy sig (env ++ [f.answer]) rest = some r ∧
        t = ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen
  all_goals simp_all

theorem effTy_gen_spec {Op : Type} (sig : Signature Op) (env : TyEnv) (body : Stmts Op) :
    ⦃⌜True⌝⦄ effTy sig env (.gen body)
    ⦃(fun t => ⌜∃ g, stmtsTy sig env false body = some g ∧
        t = ⟨g.answer.getD .unit, g.error, g.requires⟩⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen
  all_goals simp_all

/-- The inversion in the closed form (`seat-rules.md` §3.1): `∀ t, … = some t → P t` makes
`Option.of_triple`'s invariant a Miller pattern, so it is written once. -/
theorem effTy_branch_inv {Op : Type} (sig : Signature Op) (env : TyEnv)
    (test : Term) (thenB elseB : Eff Op) :
    ∀ t, effTy sig env (.branch test thenB elseB) = some t →
      termTy sig env test = some .bool ∧ ∃ a b,
        effTy sig env thenB = some a ∧ effTy sig env elseB = some b ∧
        EffTy.joinAnswer a.answer b.answer = some t.answer ∧
        t.error = a.error.join b.error ∧ t.requires = a.requires.union b.requires := by
  refine Option.of_triple ?_
  simp only [effTy]; mvcgen; all_goals simp_all

#print axioms effTy_bind_spec
#print axioms effTy_gen_spec
#print axioms effTy_branch_inv

end Conform.Spec.Probe3
