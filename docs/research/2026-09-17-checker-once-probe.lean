import Std.Tactic.Do

/-! Probe for C-P7: the type checker written ONCE, generic in the carrier of refusals.

At `Option` it is today's `effTy` (same arms, same `do` blocks, a refusal is `none`), so the
inversion lemmas keep their `mvcgen` proofs. At `Except Refusal` it is the located explanation.
That the two agree is naturality of one map, `Except.toOption`: one `simp only` per arm, no case
analysis on the reasons. No project imports. -/

set_option autoImplicit false

open Std.Do

inductive Ty where
  | nat | bool
deriving DecidableEq, Repr

inductive Reason where
  | unbound (i : Nat)
  | notBool (t : Ty)
deriving DecidableEq, Repr

structure Refusal where
  path : List Nat
  reason : Reason
deriving DecidableEq, Repr

inductive E where
  | var (i : Nat)
  | lit (n : Nat)
  | bind (first rest : E)
  | ite (test yes no : E)

/-- What a carrier of refusals offers beyond its monad: refuse with a reason, and mark that a
computation is child `i` of the node being checked. -/
class Refusing (F : Type → Type) where
  refuse : {α : Type} → Reason → F α
  under : {α : Type} → Nat → F α → F α

instance : Refusing Option where
  refuse _ := none
  under _ x := x

instance : Refusing (Except Refusal) where
  refuse r := .error ⟨[], r⟩
  under i x := match x with
    | .ok a => .ok a
    | .error r => .error { r with path := i :: r.path }

open Refusing

/-- A leaf that stays `Option`-valued (as `termTy`, `joinAnswer`, `Decision.arms` are), lifted
with the reason its failure means. -/
def orRefuse {F : Type → Type} [Monad F] [Refusing F] {α : Type} (reason : Reason) :
    Option α → F α
  | some a => pure a
  | none => refuse reason

/-- The checker, once. -/
def check {F : Type → Type} [Monad F] [Refusing F] (env : List Ty) : E → F Ty
  | .var i => orRefuse (.unbound i) env[i]?
  | .lit _ => pure .nat
  | .bind first rest => do
    let f ← under 0 (check env first)
    under 1 (check (env ++ [f]) rest)
  | .ite test yes no => do
    let t ← under 0 (check env test)
    if t = .bool then
      let a ← under 1 (check env yes)
      let _ ← under 2 (check env no)
      pure a
    else refuse (.notBool t)

/-- Today's `effTy`. -/
def ty (env : List Ty) (e : E) : Option Ty := check (F := Option) env e

/-- Today's `explainEff`, with the type it found when there is no refusal. -/
def checked (env : List Ty) (e : E) : Except Refusal Ty := check (F := Except Refusal) env e

def explain (env : List Ty) (e : E) : Option Refusal :=
  match checked env e with
  | .ok _ => none
  | .error r => some r

/-! ## The law: one map, its four equations, one `simp only` per arm -/

def toOpt {α : Type} : Except Refusal α → Option α
  | .ok a => some a
  | .error _ => none

theorem toOpt_pure {α : Type} (a : α) : toOpt (pure a : Except Refusal α) = pure a := rfl

theorem toOpt_bind {α β : Type} (x : Except Refusal α) (f : α → Except Refusal β) :
    toOpt (x >>= f) = toOpt x >>= fun a => toOpt (f a) := by
  cases x <;> rfl

theorem toOpt_refuse {α : Type} (r : Reason) :
    toOpt (refuse r : Except Refusal α) = (refuse r : Option α) := rfl

theorem toOpt_under {α : Type} (i : Nat) (x : Except Refusal α) :
    toOpt (under i x) = under i (toOpt x) := by
  cases x <;> rfl

theorem toOpt_orRefuse {α : Type} (r : Reason) (o : Option α) :
    toOpt (orRefuse (F := Except Refusal) r o) = orRefuse (F := Option) r o := by
  cases o <;> rfl

theorem toOpt_ite {α : Type} (c : Prop) [Decidable c] (x y : Except Refusal α) :
    toOpt (if c then x else y) = if c then toOpt x else toOpt y := by
  split <;> rfl

theorem check_natural (env : List Ty) (e : E) : toOpt (checked env e) = ty env e := by
  induction e generalizing env with
  | var i => simp only [checked, ty, check, toOpt_orRefuse]
  | lit n => simp only [checked, ty, check, toOpt_pure]
  | bind first rest ihf ihr =>
    simp only [checked, ty, check, toOpt_bind, toOpt_under] at ihf ihr ⊢
    simp only [ihf, ihr]
  | ite test yes no iht ihy ihn =>
    simp only [checked, ty, check, toOpt_bind, toOpt_under, toOpt_ite, toOpt_pure,
      toOpt_refuse] at iht ihy ihn ⊢
    simp only [iht, ihy, ihn]

/-- DI-86's law, now a fact about one value of `Except`. -/
theorem explain_none_iff (env : List Ty) (e : E) : explain env e = none ↔ (ty env e).isSome := by
  rw [← check_natural, explain]
  cases checked env e with
  | ok a => simp only [toOpt, Option.isSome_some]
  | error r => simp only [toOpt, Option.isSome_none, reduceCtorEq, Bool.false_eq_true]

/-! ## The `Option` instance is definitionally today's checker: the old equations by `rfl` -/

theorem ty_bind (env : List Ty) (first rest : E) :
    ty env (.bind first rest) = (do let f ← ty env first; ty (env ++ [f]) rest) := rfl

theorem ty_ite (env : List Ty) (test yes no : E) :
    ty env (.ite test yes no) = (do
      let t ← ty env test
      if t = .bool then
        let a ← ty env yes
        let _ ← ty env no
        pure a
      else none) := rfl

/-! ## An inversion lemma by `mvcgen`, through the old equation (the project's recipe) -/

theorem Option.spec_reflect {α : Type} (o : Option α) :
    ⦃⌜True⌝⦄ o ⦃(fun a => ⌜o = some a⌝, fun _ => ⌜o = none⌝, ())⦄ := by
  cases o with
  | none =>
    simp only [Triple]
    rw [show (Option.none : Option α) = (MonadExceptOf.throw () : Option α) from rfl,
      WP.throw_Option]
  | some a =>
    simp only [Triple]
    rw [show (some a : Option α) = (pure a : Option α) from rfl, WP.pure]
    simp

theorem Option.of_triple {α : Type} {o : Option α} {Inv : α → Prop}
    (h : ⦃⌜True⌝⦄ o ⦃(fun a => ⌜Inv a⌝, fun _ => ⌜True⌝, ())⦄) :
    ∀ a, o = some a → Inv a := by
  intro a ha
  subst ha
  simp only [Triple] at h
  rw [show (some a : Option α) = (pure a : Option α) from rfl, WP.pure] at h
  simpa using h

@[spec] theorem ty_reflect (env : List Ty) (e : E) :
    ⦃⌜True⌝⦄ ty env e ⦃(fun a => ⌜ty env e = some a⌝, fun _ => ⌜ty env e = none⌝, ())⦄ :=
  Option.spec_reflect _

theorem inv_bind (env : List Ty) (first rest : E) :
    ∀ t, ty env (.bind first rest) = some t →
      ∃ f, ty env first = some f ∧ ty (env ++ [f]) rest = some t := by
  refine Option.of_triple ?_
  simp only [ty_bind]; mvcgen; all_goals simp_all

/-- Variant: no per-arm equation. Unfold the generic checker at `Option`, fold the recursive
calls back to `ty` with one `rfl` lemma, and the old recipe runs. -/
theorem ty_fold (env : List Ty) (e : E) : check (F := Option) env e = ty env e := rfl
theorem under_option {α : Type} (i : Nat) (x : Option α) : under i x = x := rfl
theorem refuse_option {α : Type} (r : Reason) : (refuse r : Option α) = none := rfl

theorem inv_bind' (env : List Ty) (first rest : E) :
    ∀ t, ty env (.bind first rest) = some t →
      ∃ f, ty env first = some f ∧ ty (env ++ [f]) rest = some t := by
  refine Option.of_triple ?_
  simp only [ty, check, under_option, refuse_option]
  simp only [ty_fold]
  mvcgen; all_goals simp_all

theorem inv_ite' (env : List Ty) (test yes no : E) :
    ∀ t, ty env (.ite test yes no) = some t →
      ty env test = some .bool ∧ ty env yes = some t ∧ ∃ n, ty env no = some n := by
  refine Option.of_triple ?_
  simp only [ty, check, under_option, refuse_option]
  simp only [ty_fold]
  mvcgen; all_goals simp_all

/-! ## It runs, and the located reason is the old one -/

#guard ty [.bool] (.ite (.var 0) (.lit 1) (.lit 2)) == some .nat
#guard explain [.nat] (.bind (.lit 0) (.ite (.var 0) (.lit 1) (.lit 2)))
  == some ⟨[1], .notBool .nat⟩
#guard explain [] (.bind (.lit 0) (.ite (.lit 1) (.var 7) (.lit 2))) == some ⟨[1], .notBool .nat⟩
#guard explain [.bool] (.ite (.var 0) (.var 7) (.lit 2)) == some ⟨[1], .unbound 7⟩

/-- A typing certificate still evaluates in the kernel. -/
example : ty [.bool] (.ite (.var 0) (.lit 1) (.lit 2)) = some .nat := by decide +kernel

#print axioms check_natural
#print axioms explain_none_iff
#print axioms inv_bind
#print axioms inv_ite'
