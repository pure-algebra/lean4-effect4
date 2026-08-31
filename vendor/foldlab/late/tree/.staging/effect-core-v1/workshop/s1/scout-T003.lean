import Cas.Lang.Defun

/-!
# `EC1-T003` — forward scout probe

Stage: `lean-formalization-strategy`, **Pass A** (`.claude/skills/lean/workflows/`).
No contract exists for this row: `formal/effect-core-v1/contracts/` is scaffold
only, and `EffectCore/Foundation/Pure.lean` and `.../Value.lean` are both empty
reserved stubs. So this file freezes the QUESTION; it does not implement the row.

Row under scout (`../../PROOF-DAG.md:191`):

```text
EC1-T003  pure_eval_adequate :
    EnvWF env -> (evalPure e env = v <-> PureDenotes env e v)
```

Written 2026-08-31 against the working tree, Lean `leanprover/lean4:v4.33.1`.
Outside every lake target, exactly like `../exhibits.lean`,
`../counterexamples/LocalAnchors.lean` and `../scout/TruncCoherence.lean`. It adds
nothing to `Cas`, moves no byte, promotes no name, and mints no second carrier.

Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T003.lean
```

## What each section decides

| § | Question | Answer |
|---|---|---|
| 1 | Did the DAG's replacement escape the §3 vacuity that killed `∃! v`? | Partly. The iff is not satisfied by every relation, but it IS satisfied by the mirror relation `fun e v => evalPure e env = v`, for every function whatsoever. |
| 2 | Can `EnvWF env` be the premise? | **No.** At the estate's own pure-operand evaluator, EVERY history has a dangling operand, so no predicate on `env` alone can discharge anything. The premise must be joint in `(e, env)`. |
| 3 | Is the row's SHAPE reachable at an estate carrier? | Yes, premise-free, at `PIn.resolve` — but only with `= some v`, never `= v`. |
| 4 | Does intrinsic typing (which `EC1-D012` already mandates) remove the premise? | Yes. With `PureExpr : Context → ValueTy → Type` and a matching `Env Γ`, adequacy holds with NO well-formedness premise at all. |
| 5 | Does the row constrain a `PureAtom`'s host body? | **No.** Two different atom meanings both satisfy it while denoting different values. `ALGEBRA.md` §3 clause 5 stays owed. |

Every theorem carries a `#print axioms` receipt at the foot.
-/

namespace EC1ScoutT003

open Cas (Addr32)
open Cas.Lang

/-! ## §1 — the shape of the surviving statement

`PROOF-DAG.md:203` deleted `∃! v, evalPure e env = v` because it holds of any
Lean function. First, reproduce that (the row must not be re-argued from the
deleted form), then measure exactly how much the replacement buys. -/

section Shape

variable {α β : Type}

/-- The DELETED form, and why it was deleted: it holds of every function, so it
carries no design content. Reproduced here so this file does not rest on the
local-anchor report's `scratchpad/check3.lean`, which is not in the tree. -/
theorem deleted_form_holds_for_every_function (f : α → β) (x : α) :
    ∃ v, f x = v ∧ ∀ u, f x = u → u = v :=
  ⟨f x, rfl, fun _ h => h.symm⟩

/-- **The replacement is NOT a tautology.** Unlike `∃! v`, the two-sided iff can
fail: a relation that holds of every value is not the graph of any function into
`Bool`. So the row survives the §3 deletion as a genuine statement. -/
theorem adequacy_is_not_a_tautology :
    ∃ (f : Unit → Bool) (R : Unit → Bool → Prop), ¬ (∀ u v, f u = v ↔ R u v) := by
  refine ⟨fun _ => true, fun _ _ => True, ?_⟩
  intro h
  exact Bool.noConfusion ((h () false).mpr trivial)

/-- **What the row actually says**, stated exactly: the relation is the GRAPH of
the evaluator, pointwise. There is no room left for a second admissible
`PureDenotes`. -/
theorem adequacy_pins_the_relation (f : α → β) (R : α → β → Prop)
    (h : ∀ x v, f x = v ↔ R x v) : ∀ x v, R x v ↔ v = f x := by
  intro x v
  exact ⟨fun hR => ((h x v).mpr hR).symm, fun hv => (h x v).mp hv.symm⟩

/-- Immediate consequence, and the one piece of real content: a relational pure
semantics satisfying the row is DETERMINISTIC. A nondeterministic
`PureDenotes` is refuted by the row's own statement. -/
theorem adequacy_forces_functionality (f : α → β) (R : α → β → Prop)
    (h : ∀ x v, f x = v ↔ R x v) {x : α} {v w : β} (hv : R x v) (hw : R x w) :
    v = w :=
  ((h x v).mpr hv).symm.trans ((h x w).mpr hw)

/-- **The residual vacuity, and it is the whole cost of the row.** The mirror
relation discharges the statement for EVERY function `f`, by `Iff.rfl`. So a
green `pure_eval_adequate` is evidence about `PureDenotes` only — that it was
written independently of `evalPure` — and that independence is a REVIEW
obligation, not a Lean one. `PROOF-DAG.md` should name the independence
instrument the way `EC1-CE030`'s row names its premise. -/
theorem mirror_relation_discharges_the_row (f : α → β) :
    ∀ x v, f x = v ↔ (fun (x : α) (v : β) => f x = v) x v :=
  fun _ _ => Iff.rfl

end Shape

/-! ## §2 — `EnvWF env` cannot be the premise

`WORKSHOP-RESULTS.md:749` records that the estate already has `PureExpr` at
degenerate size: `PIn = lit | ans` with `PIn.resolve` as its total denotation
(`Cas/Lang/Defun.lean:167`, `:199`). That evaluator is `Option`-valued, and this
section proves the reason cannot be repaired by any premise on the environment. -/

section Premise

/-- At EVERY answer history there is a dangling operand: index one past the end.
This is why `PIn.resolve` answers `Option`, and it is a fact about the pair
`(operand, history)`, never about the history alone. -/
theorem resolve_dangles_at_every_env (env : List Addr32) :
    ∃ i : PIn, PIn.resolve env i = none := by
  refine ⟨.ans env.length, ?_⟩
  simp [PIn.resolve]

/-- **The premise in `EC1-T003` is the wrong shape.** For ANY candidate
`EnvWF : Env → Prop` — including `True`, including the strongest predicate
anyone can write on a history — a dangling operand still exists at every
environment the predicate admits. A unary environment premise therefore cannot
make a pure evaluator total, and cannot make the backward half of the iff
inhabited. The premise must be JOINT: a scoping/typing judgment relating `e` to
`env` (`Γ ⊢ e : τ` with `env : Env Γ`), which is what `EC1-D012
PureExpr : Context → ValueTy → Type` already asks for. -/
theorem no_unary_env_premise_totalises (EnvWF : List Addr32 → Prop) :
    ∀ env, EnvWF env → ∃ i : PIn, PIn.resolve env i = none :=
  fun env _ => resolve_dangles_at_every_env env

end Premise

/-! ## §3 — the row's shape, proved at the estate's own pure carrier

The T003 shape is reachable — with `= some v`, and with no premise at all. This
is the same split the estate keeps for its decided relations: `edgeB_iff`
(`Cas/IR/Word.lean` / `Cas/IR/Reach.lean:132`) with no premise, `reachB_iff`
(`Cas/IR/Reach.lean:541`) with one. -/

section EstateCarrier

/-- The relational reading of an operand: the inductive judgment `EC1-T003` says
`evalPure` must be adequate against. Written independently of `PIn.resolve`
(the `ans` arm speaks about membership in the history, not about the
evaluator). -/
inductive PInDenotes (env : List Addr32) : PIn → Addr32 → Prop where
  | lit (a : Addr32) : PInDenotes env (.lit a) a
  | ans {i : Nat} {a : Addr32} (h : env[i]? = some a) : PInDenotes env (.ans i) a

/-- **`EC1-T003`'s shape, at the estate's degenerate `PureExpr`.** No premise,
`Option`-valued equation. This is the statement an implementer can actually
write today. -/
theorem pin_eval_adequate (env : List Addr32) (i : PIn) (a : Addr32) :
    PIn.resolve env i = some a ↔ PInDenotes env i a := by
  cases i with
  | lit b =>
    constructor
    · intro h
      have hb : b = a := by simpa [PIn.resolve] using h
      subst hb
      exact .lit b
    · intro h
      cases h
      rfl
  | ans j =>
    constructor
    · intro h
      exact .ans (by simpa [PIn.resolve] using h)
    · intro h
      cases h with
      | ans hj => simpa [PIn.resolve] using hj

/-- The determinism the row buys, instantiated. -/
theorem pin_denotes_deterministic {env : List Addr32} {i : PIn} {a b : Addr32}
    (ha : PInDenotes env i a) (hb : PInDenotes env i b) : a = b :=
  Option.some.inj
    (((pin_eval_adequate env i a).mpr ha).symm.trans
      ((pin_eval_adequate env i b).mpr hb))

end EstateCarrier

/-! ## §4 — intrinsic typing deletes the premise

`EC1-D012` declares `PureExpr : Context → ValueTy → Type`, and `EC1-K31` forbids
a partial pure evaluator. Those two together FORCE the intrinsic reading: the
context index is what makes `evalPure` total, and once it is present there is
nothing left for `EnvWF` to say.

This is the estate's own move — `Cas/Grammar/Tree.lean:59` `Tree : Ty → Type`,
whose docstring records it: "the sort index makes an ill-kinded reference
unrepresentable".

The `many`/`PEs` arm is not decoration. `ALGEBRA.md` §3 admits "finite collection
operations with structurally smaller recursion", which forces a mutual companion
for the evaluator, for the relation, AND for the adequacy proof. That mutual
block is the real cost of this row, and the estate has already paid it once at a
DECIDER rather than an evaluator: `Cas/Schema/Ingest.lean:215` `Ast.wf_iff` with
`wfMembers_iff`/`wfFields_iff`/`wfParams_iff`. -/

section Intrinsic

/-- A miniature `ValueTy`. -/
inductive VTy where
  | unit
  | bool
  | prod : VTy → VTy → VTy
  | list : VTy → VTy

/-- A miniature `Value : ValueTy → Type`. -/
def Val : VTy → Type
  | .unit => Unit
  | .bool => Bool
  | .prod a b => Val a × Val b
  | .list a => List (Val a)

abbrev Ctx := List VTy

/-- A de Bruijn input reference. Out-of-scope is UNREPRESENTABLE. -/
inductive Var : Ctx → VTy → Type where
  | zero {Γ : Ctx} {τ : VTy} : Var (τ :: Γ) τ
  | succ {Γ : Ctx} {σ τ : VTy} : Var Γ τ → Var (σ :: Γ) τ

/-- The environment, indexed by the context it fits. There is no ill-formed
environment to exclude — `EnvWF` has no work to do here. -/
inductive Env : Ctx → Type where
  | nil : Env []
  | cons {Γ : Ctx} {τ : VTy} : Val τ → Env Γ → Env (τ :: Γ)

def Env.lookup : {Γ : Ctx} → {τ : VTy} → Env Γ → Var Γ τ → Val τ
  | _, _, .cons v _, .zero => v
  | _, _, .cons _ ρ, .succ x => Env.lookup ρ x

mutual

/-- The intrinsically typed pure expression. -/
inductive PE : Ctx → VTy → Type where
  | u    {Γ : Ctx} : PE Γ .unit
  | lit  {Γ : Ctx} (b : Bool) : PE Γ .bool
  | var  {Γ : Ctx} {τ : VTy} : Var Γ τ → PE Γ τ
  | pair {Γ : Ctx} {a b : VTy} : PE Γ a → PE Γ b → PE Γ (.prod a b)
  | fst  {Γ : Ctx} {a b : VTy} : PE Γ (.prod a b) → PE Γ a
  | many {Γ : Ctx} {a : VTy} : PEs Γ a → PE Γ (.list a)

/-- The collection companion the `many` arm forces. -/
inductive PEs : Ctx → VTy → Type where
  | nil  {Γ : Ctx} {a : VTy} : PEs Γ a
  | cons {Γ : Ctx} {a : VTy} : PE Γ a → PEs Γ a → PEs Γ a

end

mutual

/-- `evalPure`: TOTAL, structurally recursive, no fuel, no `Option`. -/
def evalPE : {Γ : Ctx} → {τ : VTy} → Env Γ → PE Γ τ → Val τ
  | _, _, _, .u => ()
  | _, _, _, .lit b => b
  | _, _, ρ, .var x => ρ.lookup x
  | _, _, ρ, .pair p q => (evalPE ρ p, evalPE ρ q)
  | _, _, ρ, .fst p => (evalPE ρ p).1
  | _, _, ρ, .many es => evalPEs ρ es

def evalPEs : {Γ : Ctx} → {a : VTy} → Env Γ → PEs Γ a → List (Val a)
  | _, _, _, .nil => []
  | _, _, ρ, .cons e es => evalPE ρ e :: evalPEs ρ es

end

mutual

/-- `PureDenotes`: the relational semantics, written by cases on the SYNTAX and
not by reference to `evalPE`. -/
inductive Den : {Γ : Ctx} → {τ : VTy} → Env Γ → PE Γ τ → Val τ → Prop where
  | u    {Γ : Ctx} (ρ : Env Γ) : Den ρ .u ()
  | lit  {Γ : Ctx} (ρ : Env Γ) (b : Bool) : Den ρ (.lit b) b
  | var  {Γ : Ctx} {τ : VTy} (ρ : Env Γ) (x : Var Γ τ) : Den ρ (.var x) (ρ.lookup x)
  | pair {Γ : Ctx} {a b : VTy} {ρ : Env Γ} {p : PE Γ a} {q : PE Γ b}
      {u : Val a} {v : Val b} : Den ρ p u → Den ρ q v → Den ρ (.pair p q) (u, v)
  | fst  {Γ : Ctx} {a b : VTy} {ρ : Env Γ} {p : PE Γ (.prod a b)}
      {u : Val a} {v : Val b} : Den ρ p (u, v) → Den ρ (.fst p) u
  | many {Γ : Ctx} {a : VTy} {ρ : Env Γ} {es : PEs Γ a} {vs : List (Val a)} :
      Dens ρ es vs → Den ρ (.many es) vs

inductive Dens : {Γ : Ctx} → {a : VTy} → Env Γ → PEs Γ a → List (Val a) → Prop where
  | nil  {Γ : Ctx} {a : VTy} (ρ : Env Γ) : Dens (a := a) ρ .nil []
  | cons {Γ : Ctx} {a : VTy} {ρ : Env Γ} {e : PE Γ a} {es : PEs Γ a}
      {v : Val a} {vs : List (Val a)} :
      Den ρ e v → Dens ρ es vs → Dens ρ (.cons e es) (v :: vs)

end

mutual

/-- Soundness half: the evaluator's answer is denoted. -/
theorem eval_sound : {Γ : Ctx} → {τ : VTy} → (ρ : Env Γ) → (e : PE Γ τ) →
    Den ρ e (evalPE ρ e)
  | _, _, ρ, .u => by simp only [evalPE]; exact .u ρ
  | _, _, ρ, .lit b => by simp only [evalPE]; exact .lit ρ b
  | _, _, ρ, .var x => by simp only [evalPE]; exact .var ρ x
  | _, _, ρ, .pair p q => by
      simp only [evalPE]; exact .pair (eval_sound ρ p) (eval_sound ρ q)
  | _, _, ρ, .fst p => by simp only [evalPE]; exact .fst (eval_sound ρ p)
  | _, _, ρ, .many es => by simp only [evalPE]; exact .many (evals_sound ρ es)

theorem evals_sound : {Γ : Ctx} → {a : VTy} → (ρ : Env Γ) → (es : PEs Γ a) →
    Dens ρ es (evalPEs ρ es)
  | _, _, ρ, .nil => by simp only [evalPEs]; exact .nil ρ
  | _, _, ρ, .cons e es => by
      simp only [evalPEs]; exact .cons (eval_sound ρ e) (evals_sound ρ es)

end

mutual

/-- Completeness half: every denoted value IS the evaluator's answer. -/
theorem eval_complete : {Γ : Ctx} → {τ : VTy} → {ρ : Env Γ} → {e : PE Γ τ} →
    {v : Val τ} → Den ρ e v → evalPE ρ e = v
  | _, _, _, _, _, .u _ => by simp only [evalPE]; rfl
  | _, _, _, _, _, .lit _ _ => by simp only [evalPE]; rfl
  | _, _, _, _, _, .var _ _ => by simp only [evalPE]
  | _, _, _, _, _, .pair hp hq => by
      simp only [evalPE, eval_complete hp, eval_complete hq]
      rfl
  | _, _, _, _, _, .fst hp => by
      simp only [evalPE, eval_complete hp]
  | _, _, _, _, _, .many hes => by
      simp only [evalPE, evals_complete hes]
      rfl

theorem evals_complete : {Γ : Ctx} → {a : VTy} → {ρ : Env Γ} → {es : PEs Γ a} →
    {vs : List (Val a)} → Dens ρ es vs → evalPEs ρ es = vs
  | _, _, _, _, _, .nil _ => by simp only [evalPEs]
  | _, _, _, _, _, .cons he hes => by
      simp only [evalPEs, eval_complete he, evals_complete hes]

end

/-- **`EC1-T003`, restated and proved.** Note what is absent: `EnvWF`. The
context index carries every well-formedness fact the theorem needs, so the
premise the DAG writes has nothing left to assume. -/
theorem pure_eval_adequate {Γ : Ctx} {τ : VTy} (ρ : Env Γ) (e : PE Γ τ)
    (v : Val τ) : evalPE ρ e = v ↔ Den ρ e v :=
  ⟨fun h => h ▸ eval_sound ρ e, eval_complete⟩

/-- The collection companion, which is a SEPARATE row the DAG does not have. -/
theorem pure_evals_adequate {Γ : Ctx} {a : VTy} (ρ : Env Γ) (es : PEs Γ a)
    (vs : List (Val a)) : evalPEs ρ es = vs ↔ Dens ρ es vs :=
  ⟨fun h => h ▸ evals_sound ρ es, evals_complete⟩

end Intrinsic

/-! ## §5 — the row is blind to a `PureAtom`'s host body

`ALGEBRA.md` §3 gives a `PureAtom` five clauses; clause 2 is a total Lean
meaning and clause 5 is a conformance obligation between that meaning and the
separately identified TypeScript body. `WORKSHOP-RESULTS.md:651` (C9) already
records that clause 5 is PENDING against a pattern the ratified law flags as
unconfronted (`EFFECTS-BACKEND.md:241`).

This section proves the sharper point: adequacy is PARAMETRIC in the atom
meaning, so `EC1-T003` cannot be the instrument that discharges clause 5, and no
amount of strengthening it will make it one. -/

section AtomOpacity

/-- A one-atom pure expression language. -/
inductive AE where
  | lit (b : Bool)
  | call : AE → AE

/-- `evalPure` with the atom's Lean meaning supplied. -/
def evalAE (g : Bool → Bool) : AE → Bool
  | .lit b => b
  | .call e => g (evalAE g e)

/-- `PureDenotes` with the same meaning supplied. -/
inductive ADen (g : Bool → Bool) : AE → Bool → Prop where
  | lit (b : Bool) : ADen g (.lit b) b
  | call {e : AE} {b : Bool} : ADen g e b → ADen g (.call e) (g b)

theorem ae_adequate (g : Bool → Bool) : ∀ (e : AE) (v : Bool),
    evalAE g e = v ↔ ADen g e v
  | .lit b, v => by
      constructor
      · rintro rfl; exact .lit b
      · intro h; cases h; rfl
  | .call e, v => by
      constructor
      · rintro rfl; exact .call ((ae_adequate g e (evalAE g e)).mp rfl)
      · intro h
        cases h with
        | call he => simp [evalAE, (ae_adequate g e _).mpr he]

/-- **The row constrains no host body.** Two DIFFERENT atom meanings each
satisfy `EC1-T003` in full, while denoting different values on the same
expression. So a green `pure_eval_adequate` is compatible with a TypeScript
`PureAtom` body that computes the wrong function. `ALGEBRA.md` §3 clause 5 needs
its own confronting instrument and cannot inherit this row. -/
theorem atom_meaning_is_unconstrained :
    (∀ e v, evalAE id e = v ↔ ADen id e v)
      ∧ (∀ e v, evalAE (fun b => !b) e = v ↔ ADen (fun b => !b) e v)
      ∧ ∃ e, evalAE id e ≠ evalAE (fun b => !b) e :=
  ⟨ae_adequate id, ae_adequate (fun b => !b),
    ⟨.call (.lit true), by decide⟩⟩

end AtomOpacity

/-! ## Receipts -/

#print axioms deleted_form_holds_for_every_function
#print axioms adequacy_is_not_a_tautology
#print axioms adequacy_pins_the_relation
#print axioms adequacy_forces_functionality
#print axioms mirror_relation_discharges_the_row
#print axioms resolve_dangles_at_every_env
#print axioms no_unary_env_premise_totalises
#print axioms pin_eval_adequate
#print axioms pin_denotes_deterministic
#print axioms eval_sound
#print axioms evals_sound
#print axioms eval_complete
#print axioms evals_complete
#print axioms pure_eval_adequate
#print axioms pure_evals_adequate
#print axioms ae_adequate
#print axioms atom_meaning_is_unconstrained

end EC1ScoutT003
