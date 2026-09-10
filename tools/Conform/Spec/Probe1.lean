import Effect4.Laws.Program.Typed
import Std.Tactic.Do

/-!
# Conform.Spec.Probe1 — does `mvcgen` split the real checker along its own structure?

The first probe of the monadic-checking pilot (`docs/research/type-tooling/`), on the real
definitions of `src/Effect4/Program/Typing.lean`, not on toys.

**Run 1 (2026-09-09 23:05).** A *generic* reflection specification for an arbitrary `Option`
program (`o` a variable) handed to `mvcgen [·]` matches the **whole `do`-block**: nothing is
decomposed and the residual goal is the plain inversion. The specification database is keyed by
the program's head symbol, so a leaf specification must name its head.

**Run 2 (23:20).** With one reflection specification *per leaf head*, the generator decomposes
every bind and introduces the leaf equations as hypotheses; what remains is the final
`some {…}` of each arm, which the generator does not recognise as `pure` (the library's
`Spec.pure` is keyed on `Pure.pure`, and `Option.some` is a different head). Two one-line
specifications, `Spec.some` and `Spec.none`, mirror `Spec.pure` and `Spec.throw_Option` for the
`Option` constructors. `Terms` is mutually inductive with `Term`, so a law about `termsTy` is a
mutual structural theorem (`induction` refuses the type), and the recursive call's specification
is a named hypothesis, not an applied term in the list.
-/

namespace Conform.Spec.Probe1

open Std.Do
open Effect4.Program

set_option linter.unusedVariables false

/-! ## The `Option` constructors as programs -/

/-- `some a` is `pure a`: the library's `Spec.pure`, keyed on the constructor. -/
@[spec] theorem Spec.some {α : Type} {a : α} {Q : PostCond α (.except PUnit .pure)} :
    ⦃Q.1 a⦄ (some a : Option α) ⦃Q⦄ := Std.Do.Spec.pure (m := Option)

/-- `none` is `throw ()`: the library's `Spec.throw_Option`, keyed on the constructor. -/
@[spec] theorem Spec.none {α : Type} {Q : PostCond α (.except PUnit .pure)} :
    ⦃Q.2.1 ()⦄ (Option.none : Option α) ⦃Q⦄ := by
  simp only [Triple]
  rw [show (Option.none : Option α) = (MonadExceptOf.throw () : Option α) from rfl,
    WP.throw_Option]

/-! ## The reflection specification, once, at `Option` -/

/-- Running an `Option` value as a program: if it answers, it was `some` of the answer; if it
fails, it was `none`. The failure clause is *permitted*, not `False`. -/
theorem Option.spec_reflect {α : Type} (o : Option α) :
    ⦃⌜True⌝⦄ o ⦃(fun a => ⌜o = some a⌝, fun _ => ⌜o = none⌝, ())⦄ := by
  cases o with
  | none =>
    simp only [Triple]
    rw [show (none : Option α) = (MonadExceptOf.throw () : Option α) from rfl, WP.throw_Option]
  | some a =>
    simp only [Triple]
    rw [show (some a : Option α) = (pure a : Option α) from rfl, WP.pure]
    simp

/-! ## Per-head instances: the leaves the checker's do-blocks call -/

theorem GenTy.joinAnswer_reflect (a b : Option Ty) :
    ⦃⌜True⌝⦄ GenTy.joinAnswer a b
    ⦃(fun r => ⌜GenTy.joinAnswer a b = some r⌝, fun _ => ⌜GenTy.joinAnswer a b = none⌝, ())⦄ :=
  Option.spec_reflect _

theorem EffTy.joinAnswer_reflect (a b : Ty) :
    ⦃⌜True⌝⦄ EffTy.joinAnswer a b
    ⦃(fun r => ⌜EffTy.joinAnswer a b = some r⌝, fun _ => ⌜EffTy.joinAnswer a b = none⌝, ())⦄ :=
  Option.spec_reflect _

theorem effTy_reflect {Op : Type} (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    ⦃⌜True⌝⦄ effTy sig env e
    ⦃(fun t => ⌜effTy sig env e = some t⌝, fun _ => ⌜effTy sig env e = none⌝, ())⦄ :=
  Option.spec_reflect _

theorem termTy_reflect {Op : Type} (sig : Signature Op) (env : TyEnv) (t : Term) :
    ⦃⌜True⌝⦄ termTy sig env t
    ⦃(fun ty => ⌜termTy sig env t = some ty⌝, fun _ => ⌜termTy sig env t = none⌝, ())⦄ :=
  Option.spec_reflect _

theorem termsTy_reflect {Op : Type} (sig : Signature Op) (env : TyEnv) (ts : Terms) :
    ⦃⌜True⌝⦄ termsTy sig env ts
    ⦃(fun tys => ⌜termsTy sig env ts = some tys⌝, fun _ => ⌜termsTy sig env ts = none⌝, ())⦄ :=
  Option.spec_reflect _

theorem atomOf_reflect {Op : Type} (sig : Signature Op) (atom : String) (tys : List Ty) :
    ⦃⌜True⌝⦄ sig.atomOf atom tys
    ⦃(fun ty => ⌜sig.atomOf atom tys = some ty⌝, fun _ => ⌜sig.atomOf atom tys = none⌝, ())⦄ :=
  Option.spec_reflect _

theorem getElem?_reflect {α : Type} (xs : List α) (i : Nat) :
    ⦃⌜True⌝⦄ xs[i]? ⦃(fun a => ⌜xs[i]? = some a⌝, fun _ => ⌜xs[i]? = none⌝, ())⦄ :=
  Option.spec_reflect _

/-! ## 1: the generator merge, with the leaf named -/

theorem merge_spec (a b : GenTy) :
    ⦃⌜True⌝⦄ GenTy.merge a b
    ⦃(fun g => ⌜GenTy.joinAnswer a.answer b.answer = some g.answer ∧
        g.error = a.error.join b.error ∧ g.requires = a.requires.union b.requires⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  unfold GenTy.merge
  mvcgen [GenTy.joinAnswer_reflect]
  all_goals simp_all

/-! ## 2: `termsTy` answers as many types as there are terms — mutual structural -/

def Terms.count : Terms → Nat
  | .nil => 0
  | .cons _ tail => Terms.count tail + 1

theorem termsTy_length_spec {Op : Type} (sig : Signature Op) (env : TyEnv) (ts : Terms) :
    ⦃⌜True⌝⦄ termsTy sig env ts
    ⦃(fun tys => ⌜tys.length = Terms.count ts⌝, fun _ => ⌜True⌝, ())⦄ := by
  cases ts with
  | nil =>
    simp only [termsTy]
    mvcgen
    all_goals simp [Terms.count]
  | cons head tail =>
    have ih := termsTy_length_spec sig env tail
    simp only [termsTy]
    mvcgen [termTy_reflect, ih]
    all_goals simp_all [Terms.count]
termination_by structural ts

/-! ## 4: the `.bind` arm of `effTy` as an inversion triple, failure permitted -/

theorem effTy_bind_spec {Op : Type} (sig : Signature Op) (env : TyEnv) (first rest : Eff Op) :
    ⦃⌜True⌝⦄ effTy sig env (.bind first rest)
    ⦃(fun t => ⌜∃ f r, effTy sig env first = some f ∧
        effTy sig (env ++ [f.answer]) rest = some r ∧
        t = ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen [effTy_reflect]
  all_goals simp_all

/-! ## 5: the `.branch` arm — an `if` inside the do-block, and a joined answer -/

theorem effTy_branch_spec {Op : Type} (sig : Signature Op) (env : TyEnv)
    (test : Term) (thenB elseB : Eff Op) :
    ⦃⌜True⌝⦄ effTy sig env (.branch test thenB elseB)
    ⦃(fun t => ⌜termTy sig env test = some .bool ∧ ∃ a b,
        effTy sig env thenB = some a ∧ effTy sig env elseB = some b ∧
        EffTy.joinAnswer a.answer b.answer = some t.answer ∧
        t.error = a.error.join b.error ∧ t.requires = a.requires.union b.requires⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen [termTy_reflect, effTy_reflect, EffTy.joinAnswer_reflect]
  all_goals simp_all

/-! ## 6: the `.perform` arm — a guard that reads the signature's domain (DI-54) -/

theorem effTy_perform_spec {Op : Type} (sig : Signature Op) (env : TyEnv) (op : Op)
    (request : Term) :
    ⦃⌜True⌝⦄ effTy sig env (.perform op request)
    ⦃(fun t => ⌜sig.dom op = true ∧ termTy sig env request = some (sig.rowOf op).request ∧
        t = ⟨(sig.rowOf op).answer, (sig.rowOf op).error,
              Effect4.Machine.Env.Requirement.ofList (sig.rowOf op).requires⟩⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen [termTy_reflect]
  all_goals simp_all

#print axioms Option.spec_reflect
#print axioms merge_spec
#print axioms termsTy_length_spec
#print axioms effTy_bind_spec
#print axioms effTy_branch_spec
#print axioms effTy_perform_spec

end Conform.Spec.Probe1
