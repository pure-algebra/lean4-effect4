import Cas.Lang.Defun

/-!
# `EC1-T003` — `pure_eval_adequate`, implemented

Slice `EC1-S1`, row `EC1-T003`. Skill stage:
`.claude/skills/lean/workflows/lean-algebraic-systems/SKILL.md` (operations,
interpreters, adequacy) — the row is an interpreter/relation adequacy statement,
not a data invariant. Its gate is answered at the foot of this file.

Row as the DAG writes it (`../../PROOF-DAG.md:191`):

```text
EC1-T003  pure_eval_adequate :
    EnvWF env -> (evalPure e env = v <-> PureDenotes env e v)
```

Written 2026-08-31 against the working tree, Lean `leanprover/lean4:v4.33.1`,
no Mathlib (`library/cas`'s `.lake/packages` is empty). This file lives OUTSIDE
every lake target, exactly like `../exhibits.lean`, `../scout/TruncCoherence.lean`
and the nine sibling scout probes. It adds nothing to `Cas`, promotes no name,
moves no byte, and mints no second `Sig`/`Prog`/`Handler`/`PProg`/`Refusal`/CAS
spelling — `EFFECTS-BACKEND.md` **R14a P1** is satisfied by construction: every
declaration here is a plain definition on first-order data, entirely outside
`Prog`.

Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/T003.lean
```

## What is proved, and how it differs from the DAG row

`EC1-D001/D002/D012/D013`, `EC1-A10 ArgMap`, `evalPure`, `PureDenotes` and
`EnvWF` **do not exist**: `formal/effect-core-v1/EffectCore/Foundation/Pure.lean`
and `.../Value.lean` are reserved stubs, and `PROOF-DAG.md` §17 conditions 1 and
13 are OPEN. So this file supplies a MODEL of the row's carriers — the full
`EC1-A08` constructor set of `ALGEBRA.md` §3 — and proves the row over it.

Three departures from the schematic signature, each forced and each proved here
rather than asserted:

1. **`EnvWF env` is DELETED, not weakened.** §2 proves that no predicate on the
   environment alone can do the premise's job at a first-order carrier, using
   the estate's own pure-operand evaluator `Cas.Lang.PIn.resolve`. §3 then
   removes the need for any premise by intrinsic typing — the estate's own move
   at `Cas/Grammar/Tree.lean:59`. `EC1-D012` already declares
   `PureExpr : Context -> ValueTy -> Type`, so this is the reading the DAG's own
   declaration table forces. §6 records that the premise-free form implies every
   premised form, so nothing is lost.
2. **The row is TWO rows.** `ALGEBRA.md` §3 admits "finite collection operations
   with structurally smaller recursion" and `EC1-A10 ArgMap`, which forces a
   mutual companion for the evaluator, the relation, and the proof.
3. **`= v` not `= some v`.** `EC1-K31` forbids a partial or fuel-bounded pure
   evaluator; §4's evaluator is total and structurally recursive, with no fuel
   and no `Option`. That is only possible at the intrinsic carrier, which is
   the same fact as departure 1.

## Section map

| § | Content |
|---|---------|
| 1 | The row's logical shape: it escapes `PROOF-DAG.md:203`'s deletion, but only conditionally. |
| 2 | Why `EnvWF env` cannot be the premise, at the estate's own pure evaluator. |
| 3 | The carrier: the full `EC1-A08` constructor set, intrinsically typed. |
| 4 | `evalPure`: total, structural, no fuel, no `Option`. |
| 5 | `PureDenotes`: inductive, one clause per constructor, no occurrence of the evaluator. |
| 6 | **`EC1-T003` and its `ArgMap` companion, proved.** Plus determinism and evaluator uniqueness. |
| 7 | Non-vacuity controls: the relation is not total, and the row has computational teeth. |
| 8 | What the row does NOT buy: a `PureAtom`'s host body is unconstrained. |
| 9 | `#print axioms` receipts. |

Every theorem carries a receipt in §9. No `sorry`, no `axiom`, no
`native_decide`, no `#eval` carrying a claim.
-/

namespace EC1T003

/-! ## §1 — the shape of the surviving statement

`PROOF-DAG.md:203` deleted `∃! v, evalPure e env = v` because it holds of any
Lean function. This section measures exactly what the replacement buys, before
any carrier is built, so the rest of the file is not arguing from the deleted
form. -/

section Shape

variable {α β : Type}

/-- The DELETED form, and why it was deleted: it holds of every function into
every type, so it carries no design content. -/
theorem deleted_form_holds_for_every_function (f : α → β) (x : α) :
    ∃ v, f x = v ∧ ∀ u, f x = u → u = v :=
  ⟨f x, rfl, fun _ h => h.symm⟩

/-- **The replacement is NOT a tautology.** Unlike `∃! v`, the two-sided iff can
fail, so `EC1-T003` survives the §3 deletion as a genuine statement. -/
theorem adequacy_is_not_a_tautology :
    ∃ (f : Unit → Bool) (R : Unit → Bool → Prop), ¬ (∀ u v, f u = v ↔ R u v) := by
  refine ⟨fun _ => true, fun _ _ => True, ?_⟩
  intro h
  exact Bool.noConfusion ((h () false).mpr trivial)

/-- What the row says in one direction: the relation is exactly the GRAPH of the
evaluator. There is no room left for a second admissible `PureDenotes`. -/
theorem adequacy_pins_the_relation (f : α → β) (R : α → β → Prop)
    (h : ∀ x v, f x = v ↔ R x v) : ∀ x v, R x v ↔ v = f x := fun x v =>
  ⟨fun hR => ((h x v).mpr hR).symm, fun hv => (h x v).mp hv.symm⟩

/-- A relational pure semantics satisfying the row is DETERMINISTIC. A
nondeterministic `PureDenotes` is refuted by the row's own statement. -/
theorem adequacy_forces_functionality (f : α → β) (R : α → β → Prop)
    (h : ∀ x v, f x = v ↔ R x v) {x : α} {v w : β} (hv : R x v) (hw : R x w) :
    v = w :=
  ((h x v).mpr hv).symm.trans ((h x w).mpr hw)

/-- **The residual vacuity, and it is the whole cost of the row.** The mirror
relation discharges the statement for EVERY function `f`, by `Iff.rfl`. So a
green `EC1-T003` is evidence about `PureDenotes` ONLY — that it was written by
cases on the syntax, independently of the evaluator. That independence is a
REVIEW obligation with no Lean instrument, and `PROOF-DAG.md` §16's Lowering row
already prohibits the mirror-image mistake ("tautological function determinism
as semantic proof"). §5 discharges the obligation by construction: no
constructor of `Den` mentions `evalPE`. -/
theorem mirror_relation_discharges_the_row (f : α → β) :
    ∀ x v, f x = v ↔ (fun (x : α) (v : β) => f x = v) x v :=
  fun _ _ => Iff.rfl

end Shape

/-! ## §2 — `EnvWF env` cannot be the premise

`WORKSHOP-RESULTS.md:749` records that the estate already owns `PureExpr` at
degenerate size: `Cas.Lang.PIn` (`Cas/Lang/Defun.lean:167`) with `PIn.resolve`
(`:199`) as its total denotation. That evaluator is `Option`-valued, and this
section proves the reason cannot be repaired by any premise on the environment.

Reuse, never mint: this section adds nothing — `PIn` and `PIn.resolve` are the
estate's, and `EXISTING-TYPES.md:71-72` dispositions them `embed`/`reuse`. -/

section Premise

open Cas (Addr32)
open Cas.Lang

/-- At EVERY answer history there is a dangling operand: index one past the end.
This is why `PIn.resolve` answers `Option`, and it is a fact about the PAIR
`(operand, history)`, never about the history alone. -/
theorem resolve_dangles_at_every_env (env : List Addr32) :
    ∃ i : PIn, PIn.resolve env i = none := by
  refine ⟨.ans env.length, ?_⟩
  simp [PIn.resolve]

/-- **The premise in `EC1-T003` is the wrong shape.** For ANY candidate
`EnvWF : Env → Prop` — including `True`, including the strongest predicate
anyone can write on a history — a dangling operand still exists at every
environment the predicate admits. A unary environment premise therefore cannot
make a pure evaluator total and cannot inhabit the backward half of the iff. The
premise must be JOINT in `(e, env)`, which is exactly what `EC1-D012
PureExpr : Context → ValueTy → Type` already asks for, and what §3 supplies.

This is `EC1-CE033`'s ruled repair (R15) at the pure fragment: restrict the
domain by a validity judgment rather than assert a premise on one argument. -/
theorem no_unary_env_premise_totalises (EnvWF : List Addr32 → Prop) :
    ∀ env, EnvWF env → ∃ i : PIn, PIn.resolve env i = none :=
  fun env _ => resolve_dangles_at_every_env env

/-- The relational reading of an operand, written independently of
`PIn.resolve`: the `ans` arm speaks about membership in the history, not about
the evaluator. -/
inductive PInDenotes (env : List Addr32) : PIn → Addr32 → Prop where
  | lit (a : Addr32) : PInDenotes env (.lit a) a
  | ans {i : Nat} {a : Addr32} (h : env[i]? = some a) : PInDenotes env (.ans i) a

/-- **The row's shape at the estate's own degenerate `PureExpr`.** No premise —
and `= some a`, never `= a`. This is the honest form at a first-order extrinsic
carrier, and `EC1-K31` forbids shipping it as the pure evaluator. -/
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

end Premise

/-! ## §3 — the carrier: `EC1-A08`'s full constructor set, intrinsically typed

`ALGEBRA.md:192-196` lists `PureExpr`'s proposed constructors: literals,
tuple/record construction and projection, sum injection and case, equality and
ordering on admitted scalar types, finite collection operations with
structurally smaller recursion, and a call to an `EC1-A09 PureAtom`. All seven
groups are present below. The scout left "the full `EC1-A08` constructor set
admits a structural evaluator" explicitly OPEN; §4 measures it and the answer is
yes, with no fuel and no well-founded recursion.

`VTy`/`Val` are a MINIATURE of `EC1-D001/D002` sufficient to state the row. They
are NOT proposed for the packet: `PROOF-DAG.md` §17 condition 13 (the supported
overlap against `Cas.Schema.El`) is OPEN, §16's Values row forbids duplicating
an inhabited `El` meaning, and `EC1-T003E` owns that bridge. Nothing here is
promoted.

Atoms are referenced BY STABLE ID through a table `Θ`, never by carrying their
meaning in the syntax. That is forced: `ALGEBRA.md` §3 clause 2 gives an atom a
total Lean meaning `Value Γ → Value τ`, and a syntax that carried a function
would collide with `EC1-T005 serialized_fields_first_order` and with R14a. The
syntax below is first-order — every `PE` node holds finite data and `Nat` ids —
while `Θ` is a semantic environment, not serialized content. -/

section Carrier

/-- Miniature `EC1-D001 ValueTy`. -/
inductive VTy where
  | unit | bool | nat
  | prod : VTy → VTy → VTy
  | sum  : VTy → VTy → VTy
  | list : VTy → VTy
  deriving DecidableEq

/-- Miniature `EC1-D002 Value`. -/
def Val : VTy → Type
  | .unit => Unit
  | .bool => Bool
  | .nat  => Nat
  | .prod a b => Val a × Val b
  | .sum a b  => Val a ⊕ Val b
  | .list a   => List (Val a)

/-- "Admitted scalar types" (`ALGEBRA.md:194`), as a finite tag carried in the
syntax. It is data, not a function, so the syntax stays first-order. -/
inductive Scalar : VTy → Type where
  | unit : Scalar .unit
  | bool : Scalar .bool
  | nat  : Scalar .nat

def boolEq (x y : Bool) : Bool :=
  Bool.or (Bool.and x y) (Bool.and (Bool.not x) (Bool.not y))

def boolLe (x y : Bool) : Bool := Bool.or (Bool.not x) y

def scalarEq : {σ : VTy} → Scalar σ → Val σ → Val σ → Bool
  | _, .unit, _, _ => true
  | _, .bool, x, y => boolEq x y
  | _, .nat,  x, y => Nat.beq x y

def scalarLe : {σ : VTy} → Scalar σ → Val σ → Val σ → Bool
  | _, .unit, _, _ => true
  | _, .bool, x, y => boolLe x y
  | _, .nat,  x, y => Nat.ble x y

/-- Non-dependent sum eliminator. Written out rather than left as a `match` so
that `evalPE`'s equation for `case` is an ordinary application and the proofs do
not have to name an auxiliary matcher. -/
def sumElim {α β γ : Type} (f : α → γ) (g : β → γ) : α ⊕ β → γ
  | .inl a => f a
  | .inr b => g b

abbrev Ctx := List VTy

/-- A de Bruijn input reference. An out-of-scope reference is
UNREPRESENTABLE — the estate's own move at `Cas/Grammar/Tree.lean:59`, whose
docstring records it: "the sort index makes an ill-kinded reference
unrepresentable". This is what deletes `EnvWF`. -/
inductive Var : Ctx → VTy → Type where
  | zero {Γ : Ctx} {τ : VTy} : Var (τ :: Γ) τ
  | succ {Γ : Ctx} {σ τ : VTy} : Var Γ τ → Var (σ :: Γ) τ

/-- The environment, indexed by the context it fits. There is no ill-formed
environment to exclude. -/
inductive Env : Ctx → Type where
  | nil : Env []
  | cons {Γ : Ctx} {τ : VTy} : Val τ → Env Γ → Env (τ :: Γ)

def Env.lookup : {Γ : Ctx} → {τ : VTy} → Env Γ → Var Γ τ → Val τ
  | _, _, .cons v _, .zero => v
  | _, _, .cons _ ρ, .succ x => Env.lookup ρ x

/-- One `EC1-A09 PureAtom` row's type, clause 1. -/
structure AtomSig where
  args : Ctx
  ret  : VTy

/-- The atom table: clause 1 (identity and type) plus clause 2 (a TOTAL Lean
meaning). Clauses 3-5 — the separately identified TypeScript body and its
conformance obligation — are deliberately absent, and §8 proves that no
strengthening of `EC1-T003` can reach them. -/
structure AtomTable where
  sig : Nat → AtomSig
  meaning : (n : Nat) → Env (sig n).args → Val (sig n).ret

mutual

/-- `EC1-D012 PureExpr : Context → ValueTy → Type`, with `ALGEBRA.md:192-196`'s
full constructor set. -/
inductive PE (Θ : AtomTable) : Ctx → VTy → Type where
  /-- literals (on admitted scalars) -/
  | lit  {Γ : Ctx} {σ : VTy} (s : Scalar σ) (v : Val σ) : PE Θ Γ σ
  /-- typed input reference -/
  | var  {Γ : Ctx} {τ : VTy} (x : Var Γ τ) : PE Θ Γ τ
  /-- tuple/record construction -/
  | pair {Γ : Ctx} {a b : VTy} : PE Θ Γ a → PE Θ Γ b → PE Θ Γ (.prod a b)
  /-- tuple/record projection -/
  | fst  {Γ : Ctx} {a b : VTy} : PE Θ Γ (.prod a b) → PE Θ Γ a
  | snd  {Γ : Ctx} {a b : VTy} : PE Θ Γ (.prod a b) → PE Θ Γ b
  /-- sum injection -/
  | inl  {Γ : Ctx} {a b : VTy} : PE Θ Γ a → PE Θ Γ (.sum a b)
  | inr  {Γ : Ctx} {a b : VTy} : PE Θ Γ b → PE Θ Γ (.sum a b)
  /-- sum case -/
  | case {Γ : Ctx} {a b c : VTy} :
      PE Θ Γ (.sum a b) → PE Θ (a :: Γ) c → PE Θ (b :: Γ) c → PE Θ Γ c
  /-- equality on an admitted scalar type -/
  | eqs  {Γ : Ctx} {σ : VTy} (s : Scalar σ) : PE Θ Γ σ → PE Θ Γ σ → PE Θ Γ .bool
  /-- ordering on an admitted scalar type -/
  | les  {Γ : Ctx} {σ : VTy} (s : Scalar σ) : PE Θ Γ σ → PE Θ Γ σ → PE Θ Γ .bool
  /-- finite collection construction -/
  | nil  {Γ : Ctx} {a : VTy} : PE Θ Γ (.list a)
  | cons {Γ : Ctx} {a : VTy} : PE Θ Γ a → PE Θ Γ (.list a) → PE Θ Γ (.list a)
  /-- the finite collection operation, with the recursion carried by the
  collection rather than by the syntax (`EC1-K31`'s "explicit collection-size
  measure"); the step body binds accumulator then element. -/
  | fold {Γ : Ctx} {a b : VTy} :
      PE Θ Γ (.list a) → PE Θ Γ b → PE Θ (b :: a :: Γ) b → PE Θ Γ b
  /-- a call to an `EC1-A09 PureAtom`, by stable id, with an `EC1-A10 ArgMap`. -/
  | atom {Γ : Ctx} (n : Nat) : Args Θ Γ (Θ.sig n).args → PE Θ Γ (Θ.sig n).ret

/-- `EC1-A10 ArgMap Γ Δ`: one `PureExpr Γ τ` for every destination parameter
`τ` in `Δ`. -/
inductive Args (Θ : AtomTable) : Ctx → Ctx → Type where
  | nil  {Γ : Ctx} : Args Θ Γ []
  | cons {Γ : Ctx} {τ : VTy} {Δ : Ctx} : PE Θ Γ τ → Args Θ Γ Δ → Args Θ Γ (τ :: Δ)

end

end Carrier

/-! ## §4 — `evalPure`, total and structural

`EC1-K31` (`CONTRACT-PACKET.md:625-629`): "`PureExpr` recursion decreases
structurally or by an explicit collection-size measure... There is no partial or
fuel-bounded 'pure' evaluator." Both halves hold below: the recursion is
structural in the expression, the `fold` arm's recursion is carried by
`List.foldl` over the evaluated collection, and the result type is `Val τ` — no
`Option`, no fuel index.

This is the measurement the scout left explicitly open ("NOT that the full
`EC1-A08` constructor set admits a structural evaluator; that remains open and
is the one thing an implementer should re-measure first"). It comes out clean:
Lean accepts the definition by STRUCTURAL recursion with no `termination_by` and
no `decreasing_by`, INCLUDING the `fold` arm's recursive call under a lambda —
`#print evalPE` shows `PE.brecOn`, not `WellFounded.fix`, and `rfl` reduces
closed applications (`caseProj_evaluates`, `sumFold_evaluates`), which a
well-founded definition would not permit. `EC1-K31`'s alternative "explicit
collection-size measure" is therefore not needed at the syntax level; the
collection recursion lives in `List.foldl` over the evaluated collection. -/

section Evaluator

mutual

def evalPE (Θ : AtomTable) : {Γ : Ctx} → {τ : VTy} → Env Γ → PE Θ Γ τ → Val τ
  | _, _, _, .lit _ v => v
  | _, _, ρ, .var x => ρ.lookup x
  | _, _, ρ, .pair p q => (evalPE Θ ρ p, evalPE Θ ρ q)
  | _, _, ρ, .fst p => (evalPE Θ ρ p).1
  | _, _, ρ, .snd p => (evalPE Θ ρ p).2
  | _, _, ρ, .inl p => Sum.inl (evalPE Θ ρ p)
  | _, _, ρ, .inr p => Sum.inr (evalPE Θ ρ p)
  | _, _, ρ, .case p l r =>
      sumElim (fun u => evalPE Θ (.cons u ρ) l) (fun u => evalPE Θ (.cons u ρ) r)
        (evalPE Θ ρ p)
  | _, _, ρ, .eqs s p q => scalarEq s (evalPE Θ ρ p) (evalPE Θ ρ q)
  | _, _, ρ, .les s p q => scalarLe s (evalPE Θ ρ p) (evalPE Θ ρ q)
  | _, _, _, .nil => []
  | _, _, ρ, .cons p ps => evalPE Θ ρ p :: evalPE Θ ρ ps
  | _, _, ρ, .fold xs e0 step =>
      (evalPE Θ ρ xs).foldl
        (fun acc x => evalPE Θ (.cons acc (.cons x ρ)) step) (evalPE Θ ρ e0)
  | _, _, ρ, .atom n as => Θ.meaning n (evalArgs Θ ρ as)

/-- The `EC1-A10 ArgMap` companion evaluator. -/
def evalArgs (Θ : AtomTable) : {Γ Δ : Ctx} → Env Γ → Args Θ Γ Δ → Env Δ
  | _, _, _, .nil => .nil
  | _, _, ρ, .cons p ps => .cons (evalPE Θ ρ p) (evalArgs Θ ρ ps)

end

end Evaluator

/-! ## §5 — `PureDenotes`, written independently of the evaluator

`ALGEBRA.md:210-212`: "The pure fragment also has an inductive
`PureDenotes env e v` judgment. `evalPure` is accepted only with a two-way
adequacy theorem against that judgment."

§1's `mirror_relation_discharges_the_row` names the only way this row can be
cheated: define the relation as the evaluator's graph and the theorem is
`Iff.rfl`. The review gate is structural and it is met here by inspection —
**no constructor below mentions `evalPE` or `evalArgs`**. Each clause is by
cases on the syntax; `scalarEq`/`scalarLe`/`Θ.meaning` appear because they are
the DENOTATIONS of their operations (the value algebra and `EC1-A09` clause 2),
not the evaluator.

`DenFold` is the collection judgment the `fold` arm forces. It is mutual with
`Den` and `Dens` because `Den`'s `fold` clause needs it and its own `cons`
clause needs `Den` at the step body. -/

section Relation

mutual

/-- `EC1-D0xx PureDenotes`. -/
inductive Den (Θ : AtomTable) : {Γ : Ctx} → {τ : VTy} → Env Γ → PE Θ Γ τ → Val τ → Prop where
  | lit {Γ : Ctx} {σ : VTy} (ρ : Env Γ) (s : Scalar σ) (v : Val σ) :
      Den Θ ρ (.lit s v) v
  | var {Γ : Ctx} {τ : VTy} (ρ : Env Γ) (x : Var Γ τ) :
      Den Θ ρ (.var x) (ρ.lookup x)
  | pair {Γ : Ctx} {a b : VTy} {ρ : Env Γ} {p : PE Θ Γ a} {q : PE Θ Γ b}
      {u : Val a} {v : Val b} :
      Den Θ ρ p u → Den Θ ρ q v → Den Θ ρ (.pair p q) (u, v)
  | fst {Γ : Ctx} {a b : VTy} {ρ : Env Γ} {p : PE Θ Γ (.prod a b)}
      {u : Val a} {v : Val b} : Den Θ ρ p (u, v) → Den Θ ρ (.fst p) u
  | snd {Γ : Ctx} {a b : VTy} {ρ : Env Γ} {p : PE Θ Γ (.prod a b)}
      {u : Val a} {v : Val b} : Den Θ ρ p (u, v) → Den Θ ρ (.snd p) v
  | inl {Γ : Ctx} {a b : VTy} {ρ : Env Γ} {p : PE Θ Γ a} {u : Val a} :
      Den Θ ρ p u → Den Θ ρ (.inl (b := b) p) (Sum.inl u)
  | inr {Γ : Ctx} {a b : VTy} {ρ : Env Γ} {p : PE Θ Γ b} {u : Val b} :
      Den Θ ρ p u → Den Θ ρ (.inr (a := a) p) (Sum.inr u)
  | caseL {Γ : Ctx} {a b c : VTy} {ρ : Env Γ} {p : PE Θ Γ (.sum a b)}
      {l : PE Θ (a :: Γ) c} {r : PE Θ (b :: Γ) c} {u : Val a} {w : Val c} :
      Den Θ ρ p (Sum.inl u) → Den Θ (.cons u ρ) l w → Den Θ ρ (.case p l r) w
  | caseR {Γ : Ctx} {a b c : VTy} {ρ : Env Γ} {p : PE Θ Γ (.sum a b)}
      {l : PE Θ (a :: Γ) c} {r : PE Θ (b :: Γ) c} {u : Val b} {w : Val c} :
      Den Θ ρ p (Sum.inr u) → Den Θ (.cons u ρ) r w → Den Θ ρ (.case p l r) w
  | eqs {Γ : Ctx} {σ : VTy} {ρ : Env Γ} (s : Scalar σ) {p q : PE Θ Γ σ}
      {u v : Val σ} :
      Den Θ ρ p u → Den Θ ρ q v → Den Θ ρ (.eqs s p q) (scalarEq s u v)
  | les {Γ : Ctx} {σ : VTy} {ρ : Env Γ} (s : Scalar σ) {p q : PE Θ Γ σ}
      {u v : Val σ} :
      Den Θ ρ p u → Den Θ ρ q v → Den Θ ρ (.les s p q) (scalarLe s u v)
  | nil {Γ : Ctx} {a : VTy} (ρ : Env Γ) :
      Den Θ ρ (PE.nil (a := a)) ([] : List (Val a))
  | cons {Γ : Ctx} {a : VTy} {ρ : Env Γ} {p : PE Θ Γ a} {ps : PE Θ Γ (.list a)}
      {u : Val a} {us : List (Val a)} :
      Den Θ ρ p u → Den Θ ρ ps us → Den Θ ρ (.cons p ps) (u :: us)
  | fold {Γ : Ctx} {a b : VTy} {ρ : Env Γ} {xs : PE Θ Γ (.list a)}
      {e0 : PE Θ Γ b} {step : PE Θ (b :: a :: Γ) b}
      {vs : List (Val a)} {acc r : Val b} :
      Den Θ ρ xs vs → Den Θ ρ e0 acc → DenFold Θ ρ step vs acc r →
      Den Θ ρ (.fold xs e0 step) r
  | atom {Γ : Ctx} {ρ : Env Γ} {n : Nat} {as : Args Θ Γ (Θ.sig n).args}
      {ρ' : Env (Θ.sig n).args} :
      Dens Θ ρ as ρ' → Den Θ ρ (.atom n as) (Θ.meaning n ρ')

/-- The `EC1-A10 ArgMap` judgment. -/
inductive Dens (Θ : AtomTable) : {Γ Δ : Ctx} → Env Γ → Args Θ Γ Δ → Env Δ → Prop where
  | nil {Γ : Ctx} (ρ : Env Γ) : Dens Θ ρ Args.nil Env.nil
  | cons {Γ : Ctx} {τ : VTy} {Δ : Ctx} {ρ : Env Γ} {p : PE Θ Γ τ}
      {ps : Args Θ Γ Δ} {v : Val τ} {ρ' : Env Δ} :
      Den Θ ρ p v → Dens Θ ρ ps ρ' → Dens Θ ρ (.cons p ps) (.cons v ρ')

/-- The finite-collection judgment: `DenFold Θ ρ step vs acc r` says folding
`step` over `vs` from `acc` denotes `r`. -/
inductive DenFold (Θ : AtomTable) :
    {Γ : Ctx} → {a b : VTy} → Env Γ → PE Θ (b :: a :: Γ) b →
    List (Val a) → Val b → Val b → Prop where
  | nil {Γ : Ctx} {a b : VTy} {ρ : Env Γ} {step : PE Θ (b :: a :: Γ) b}
      {acc : Val b} : DenFold Θ ρ step ([] : List (Val a)) acc acc
  | cons {Γ : Ctx} {a b : VTy} {ρ : Env Γ} {step : PE Θ (b :: a :: Γ) b}
      {x : Val a} {xs : List (Val a)} {acc acc' r : Val b} :
      Den Θ (.cons acc (.cons x ρ)) step acc' →
      DenFold Θ ρ step xs acc' r →
      DenFold Θ ρ step (x :: xs) acc r

end

end Relation

/-! ## §6 — `EC1-T003`, proved

The route is the estate's own split at `Cas/IR/Reach.lean:531/535/541`
(`reachB_sound` / `reachB_complete` / `reachB_iff`), and the mutual cost is the
one the estate already paid at a DECIDER in `Cas/Schema/Ingest.lean:215`
(`Ast.wf_iff` plus six companions). Two-sided adequacy in one `iff` is the
estate's flagship shape at `Cas/Core/Admission.lean:60` (`checkRefs_ok_iff`).

The two collection lemmas are stated OUTSIDE the mutual blocks, parameterised by
the step body's adequacy. That is what keeps the mutual recursion structural:
every recursive call is on a syntactic subterm, and the collection recursion is
an ordinary induction on the evaluated list. -/

section Adequacy

variable {Θ : AtomTable}

/-- Soundness for the collection arm, given soundness at the step body. -/
theorem denFold_of_foldl {Γ : Ctx} {a b : VTy} (ρ : Env Γ)
    (step : PE Θ (b :: a :: Γ) b)
    (hstep : ∀ ρ' : Env (b :: a :: Γ), Den Θ ρ' step (evalPE Θ ρ' step)) :
    ∀ (vs : List (Val a)) (acc : Val b),
      DenFold Θ ρ step vs acc
        (vs.foldl (fun c x => evalPE Θ (.cons c (.cons x ρ)) step) acc) := by
  intro vs
  induction vs with
  | nil => intro acc; exact .nil
  | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons]
      exact .cons (hstep (.cons acc (.cons x ρ))) (ih _)

mutual

/-- **Soundness half.** The evaluator's answer is denoted. -/
theorem eval_sound (Θ : AtomTable) : {Γ : Ctx} → {τ : VTy} → (ρ : Env Γ) →
    (e : PE Θ Γ τ) → Den Θ ρ e (evalPE Θ ρ e)
  | _, _, ρ, .lit s v => by simp only [evalPE]; exact .lit ρ s v
  | _, _, ρ, .var x => by simp only [evalPE]; exact .var ρ x
  | _, _, ρ, .pair p q => by
      simp only [evalPE]; exact .pair (eval_sound Θ ρ p) (eval_sound Θ ρ q)
  | _, _, ρ, .fst p => by simp only [evalPE]; exact .fst (eval_sound Θ ρ p)
  | _, _, ρ, .snd p => by simp only [evalPE]; exact .snd (eval_sound Θ ρ p)
  | _, _, ρ, .inl p => by simp only [evalPE]; exact .inl (eval_sound Θ ρ p)
  | _, _, ρ, .inr p => by simp only [evalPE]; exact .inr (eval_sound Θ ρ p)
  | _, _, ρ, .case p l r => by
      have hp := eval_sound Θ ρ p
      simp only [evalPE]
      revert hp
      generalize evalPE Θ ρ p = w
      intro hp
      cases w with
      | inl u => exact .caseL hp (eval_sound Θ (.cons u ρ) l)
      | inr u => exact .caseR hp (eval_sound Θ (.cons u ρ) r)
  | _, _, ρ, .eqs s p q => by
      simp only [evalPE]; exact .eqs s (eval_sound Θ ρ p) (eval_sound Θ ρ q)
  | _, _, ρ, .les s p q => by
      simp only [evalPE]; exact .les s (eval_sound Θ ρ p) (eval_sound Θ ρ q)
  | _, _, ρ, .nil => by simp only [evalPE]; exact .nil ρ
  | _, _, ρ, .cons p ps => by
      simp only [evalPE]; exact .cons (eval_sound Θ ρ p) (eval_sound Θ ρ ps)
  | _, _, ρ, .fold xs e0 step => by
      simp only [evalPE]
      exact .fold (eval_sound Θ ρ xs) (eval_sound Θ ρ e0)
        (denFold_of_foldl ρ step (fun ρ' => eval_sound Θ ρ' step) _ _)
  | _, _, ρ, .atom n as => by
      simp only [evalPE]; exact .atom (evalArgs_sound Θ ρ as)

theorem evalArgs_sound (Θ : AtomTable) : {Γ Δ : Ctx} → (ρ : Env Γ) →
    (as : Args Θ Γ Δ) → Dens Θ ρ as (evalArgs Θ ρ as)
  | _, _, ρ, .nil => by simp only [evalArgs]; exact .nil ρ
  | _, _, ρ, .cons p ps => by
      simp only [evalArgs]; exact .cons (eval_sound Θ ρ p) (evalArgs_sound Θ ρ ps)

end

mutual

/-- **Completeness half.** Every denoted value IS the evaluator's answer.
Recursion is on the DERIVATION, mutually across all three judgments — the
`reachB_complete` half of `Cas/IR/Reach.lean`'s split, at a three-family mutual
syntax rather than a single relation. -/
theorem eval_complete (Θ : AtomTable) : {Γ : Ctx} → {τ : VTy} → {ρ : Env Γ} →
    {e : PE Θ Γ τ} → {v : Val τ} → Den Θ ρ e v → evalPE Θ ρ e = v
  | _, _, _, _, _, .lit _ _ _ => by simp only [evalPE] <;> rfl
  | _, _, _, _, _, .var _ _ => by simp only [evalPE] <;> rfl
  | _, _, _, _, _, .pair hp hq => by
      simp only [evalPE, eval_complete Θ hp, eval_complete Θ hq] <;> rfl
  | _, _, _, _, _, .fst hp => by simp only [evalPE, eval_complete Θ hp] <;> rfl
  | _, _, _, _, _, .snd hp => by simp only [evalPE, eval_complete Θ hp] <;> rfl
  | _, _, _, _, _, .inl hp => by simp only [evalPE, eval_complete Θ hp] <;> rfl
  | _, _, _, _, _, .inr hp => by simp only [evalPE, eval_complete Θ hp] <;> rfl
  | _, _, _, _, _, .caseL hp hl => by
      simp only [evalPE, eval_complete Θ hp, sumElim]
      exact eval_complete Θ hl
  | _, _, _, _, _, .caseR hp hr => by
      simp only [evalPE, eval_complete Θ hp, sumElim]
      exact eval_complete Θ hr
  | _, _, _, _, _, .eqs _ hp hq => by
      simp only [evalPE, eval_complete Θ hp, eval_complete Θ hq] <;> rfl
  | _, _, _, _, _, .les _ hp hq => by
      simp only [evalPE, eval_complete Θ hp, eval_complete Θ hq] <;> rfl
  | _, _, _, _, _, .nil _ => by simp only [evalPE] <;> rfl
  | _, _, _, _, _, .cons hp hps => by
      simp only [evalPE, eval_complete Θ hp, eval_complete Θ hps] <;> rfl
  | _, _, _, _, _, .fold hxs he0 hf => by
      simp only [evalPE, eval_complete Θ hxs, eval_complete Θ he0]
      exact evalFold_complete Θ hf
  | _, _, _, _, _, .atom has => by
      simp only [evalPE, evalArgs_complete Θ has] <;> rfl

/-- The `EC1-A10 ArgMap` companion. -/
theorem evalArgs_complete (Θ : AtomTable) : {Γ Δ : Ctx} → {ρ : Env Γ} →
    {as : Args Θ Γ Δ} → {ρ' : Env Δ} → Dens Θ ρ as ρ' → evalArgs Θ ρ as = ρ'
  | _, _, _, _, _, .nil _ => by simp only [evalArgs] <;> rfl
  | _, _, _, _, _, .cons hp hps => by
      simp only [evalArgs, eval_complete Θ hp, evalArgs_complete Θ hps] <;> rfl

/-- The finite-collection companion: the third judgment the `fold` arm forces. -/
theorem evalFold_complete (Θ : AtomTable) : {Γ : Ctx} → {a b : VTy} →
    {ρ : Env Γ} → {step : PE Θ (b :: a :: Γ) b} → {vs : List (Val a)} →
    {acc r : Val b} → DenFold Θ ρ step vs acc r →
    vs.foldl (fun c x => evalPE Θ (.cons c (.cons x ρ)) step) acc = r
  | _, _, _, _, _, _, _, _, .nil => by simp only [List.foldl_nil] <;> rfl
  | _, _, _, _, _, _, _, _, .cons hs hf => by
      simp only [List.foldl_cons, eval_complete Θ hs]
      exact evalFold_complete Θ hf

end

/-- **`EC1-T003 pure_eval_adequate`, proved.**

Note what is absent: `EnvWF`. §2 proves no unary environment predicate can do
its job; §3's context index carries every well-formedness fact the theorem
needs; and `premise_free_implies_any_EnvWF` below shows the premise-free form
implies every premised form, so the deletion loses nothing. -/
theorem pure_eval_adequate (Θ : AtomTable) {Γ : Ctx} {τ : VTy}
    (ρ : Env Γ) (e : PE Θ Γ τ) (v : Val τ) :
    evalPE Θ ρ e = v ↔ Den Θ ρ e v :=
  ⟨fun h => h ▸ eval_sound Θ ρ e, eval_complete Θ⟩

/-- **The `EC1-A10 ArgMap` companion**, which the DAG has no row for and which
`ALGEBRA.md` §3's admission of "finite collection operations" plus `ArgMap`
makes mandatory: the mutual syntax forces a mutual evaluator, a mutual relation,
and a mutual proof. -/
theorem pure_evalArgs_adequate (Θ : AtomTable) {Γ Δ : Ctx}
    (ρ : Env Γ) (as : Args Θ Γ Δ) (ρ' : Env Δ) :
    evalArgs Θ ρ as = ρ' ↔ Dens Θ ρ as ρ' :=
  ⟨fun h => h ▸ evalArgs_sound Θ ρ as, evalArgs_complete Θ⟩

/-- Cheap consequence, unstated in the DAG: the pure semantics is
DETERMINISTIC. This is the row's real content, instantiated. -/
theorem pure_denotes_deterministic (Θ : AtomTable) {Γ : Ctx} {τ : VTy}
    {ρ : Env Γ} {e : PE Θ Γ τ} {v w : Val τ}
    (hv : Den Θ ρ e v) (hw : Den Θ ρ e w) : v = w :=
  ((pure_eval_adequate Θ ρ e v).mpr hv).symm.trans
    ((pure_eval_adequate Θ ρ e w).mpr hw)

/-- The other half of what adequacy buys, and the sharper statement: the
relation determines the EVALUATOR uniquely. Any candidate `f` satisfying the row
against `Den` is `evalPE` pointwise, so a green `EC1-T003` leaves no freedom on
the computational side either. -/
theorem adequacy_pins_the_evaluator (Θ : AtomTable)
    (f : {Γ : Ctx} → {τ : VTy} → Env Γ → PE Θ Γ τ → Val τ)
    (h : ∀ {Γ : Ctx} {τ : VTy} (ρ : Env Γ) (e : PE Θ Γ τ) (v : Val τ),
        f ρ e = v ↔ Den Θ ρ e v)
    {Γ : Ctx} {τ : VTy} (ρ : Env Γ) (e : PE Θ Γ τ) : f ρ e = evalPE Θ ρ e :=
  (h ρ e (evalPE Θ ρ e)).mpr (eval_sound Θ ρ e)

/-- Deleting the premise is a STRENGTHENING, not a weakening: the premise-free
row implies the row under any environment predicate whatsoever, including the
`EnvWF` the DAG names. -/
theorem premise_free_implies_any_EnvWF (Θ : AtomTable)
    (EnvWF : {Γ : Ctx} → Env Γ → Prop) {Γ : Ctx} {τ : VTy}
    (ρ : Env Γ) (_ : EnvWF ρ) (e : PE Θ Γ τ) (v : Val τ) :
    evalPE Θ ρ e = v ↔ Den Θ ρ e v :=
  pure_eval_adequate Θ ρ e v

end Adequacy

/-! ## §7 — non-vacuity controls

`PROOF-DAG.md` §16's Checker row prohibits "using successful examples as
completeness", so the examples below are not offered as evidence FOR the row.
They are the gate's positive scenarios (the algebraic-systems stage requires
both) plus two adversaries that show the row is not satisfied by everything.

The adversary is the estate's standard one for this shape: the DISCARDING
interpreter, which `Cas/Backend/Canon.lean:199-215` names in its own docstring
("a canonicalizer that THROWS SERVICES AWAY") and which `EC1-T001`'s scout
showed satisfies a bare idempotence row. Adequacy refuses it. -/

section Controls

/-- `Val` is an ordinary `def`, so instance synthesis does not see through it
and `(7 : Val .nat)` has no `OfNat`. These three move a host literal in and a
`nat` answer out, at default transparency. They are notation, not content. -/
def natV (n : Nat) : Val .nat := n
def boolV (b : Bool) : Val .bool := b
def natOut (v : Val .nat) : Nat := v

/-- One `EC1-A09 PureAtom` signature: id 0 is binary on `nat`; every other id
has the empty signature. -/
def demoSig : Nat → AtomSig
  | 0 => ⟨[.nat, .nat], .nat⟩
  | _ => ⟨[], .unit⟩

/-- Clause 2 for that atom: addition. -/
def demoAdd : (n : Nat) → Env (demoSig n).args → Val (demoSig n).ret
  | 0 => fun ρ => Nat.add (ρ.lookup .zero) (ρ.lookup (.succ .zero))
  | _ + 1 => fun _ => ()

/-- The SAME signature, a different body: multiplication. §8 turns this pair
into a theorem about what the row cannot see. -/
def demoMul : (n : Nat) → Env (demoSig n).args → Val (demoSig n).ret
  | 0 => fun ρ => Nat.mul (ρ.lookup .zero) (ρ.lookup (.succ .zero))
  | _ + 1 => fun _ => ()

def addTable : AtomTable := ⟨demoSig, demoAdd⟩
def mulTable : AtomTable := ⟨demoSig, demoMul⟩

/-- A program exercising every constructor group that carries a binder or a
collection: `fold` over a literal list, an atom call through an `EC1-A10
ArgMap`, and two input references (accumulator and element). -/
def sumFold : PE addTable [] .nat :=
  PE.fold
    (.cons (.lit .nat (natV 1)) (.cons (.lit .nat (natV 2))
      (.cons (.lit .nat (natV 3)) .nil)))
    (.lit .nat (natV 0))
    (PE.atom 0 (Args.cons (.var .zero) (Args.cons (.var (.succ .zero)) Args.nil)))

/-- Character-for-character the same program at the multiplication table. It is
a DIFFERENT type, because `PE` is indexed by its table — which is the point:
the syntax is shared, the meaning is not. -/
def mulFold : PE mulTable [] .nat :=
  PE.fold
    (.cons (.lit .nat (natV 1)) (.cons (.lit .nat (natV 2))
      (.cons (.lit .nat (natV 3)) .nil)))
    (.lit .nat (natV 0))
    (PE.atom 0 (Args.cons (.var .zero) (Args.cons (.var (.succ .zero)) Args.nil)))

/-- A program exercising sum injection, sum case, tuple construction and tuple
projection. -/
def caseProj : PE addTable [] .nat :=
  PE.case (a := .prod .nat .bool) (b := .unit)
    (PE.inl (PE.pair (.lit .nat (natV 7)) (.lit .bool (boolV true))))
    (PE.fst (PE.var .zero))
    (.lit .nat (natV 0))

/-- Positive scenario, computational face. -/
theorem caseProj_evaluates : evalPE addTable .nil caseProj = natV 7 := rfl

/-- Positive scenario, relational face — obtained FROM the row, which is the
only honest way to get one. -/
theorem caseProj_denotes : Den addTable .nil caseProj (natV 7) :=
  (pure_eval_adequate addTable .nil caseProj (natV 7)).mp caseProj_evaluates

theorem sumFold_evaluates : natOut (evalPE addTable .nil sumFold) = 6 := rfl

theorem mulFold_evaluates : natOut (evalPE mulTable .nil mulFold) = 0 := rfl

/-- The interpreter equation for the collection arm, written out: the recursion
is carried by the evaluated collection, which is `EC1-K31`'s "explicit
collection-size measure". -/
theorem evalPE_fold (Θ : AtomTable) {Γ : Ctx} {a b : VTy} (ρ : Env Γ)
    (xs : PE Θ Γ (.list a)) (e0 : PE Θ Γ b) (step : PE Θ (b :: a :: Γ) b) :
    evalPE Θ ρ (.fold xs e0 step)
      = (evalPE Θ ρ xs).foldl
          (fun c x => evalPE Θ (.cons c (.cons x ρ)) step) (evalPE Θ ρ e0) := by
  simp only [evalPE]

/-- A total default value at every type code — the discarding interpreter's
answer. -/
def defaultVal : (τ : VTy) → Val τ
  | .unit => ()
  | .bool => false
  | .nat => natV 0
  | .prod a b => (defaultVal a, defaultVal b)
  | .sum a _ => Sum.inl (defaultVal a)
  | .list _ => []

/-- The relation is NOT the total relation: it refuses a value the syntax does
not denote. Proved through the row rather than by inversion, because `Den`'s
`atom` clause indexes on `(Θ.sig n).ret` and dependent elimination cannot refute
`VTy.bool = (Θ.sig n).ret` for an opaque table. -/
theorem den_is_not_total (Θ : AtomTable) :
    ¬ Den Θ Env.nil (PE.lit (Θ := Θ) (Γ := []) .bool true) false := by
  intro h
  have hv := (pure_eval_adequate Θ Env.nil (PE.lit .bool true) false).mpr h
  simp only [evalPE] at hv
  exact Bool.noConfusion hv

/-- **The discarding interpreter fails the row.** `EC1-T001`'s scout showed a
bare idempotence row is satisfied by a normalizer that throws everything away;
the two-sided adequacy iff is not. This is the concrete reason `EC1-T003` is
worth having and `∃! v, evalPure e env = v` was not. -/
theorem discarding_evaluator_fails_adequacy (Θ : AtomTable) :
    ¬ (∀ {Γ : Ctx} {τ : VTy} (ρ : Env Γ) (e : PE Θ Γ τ) (v : Val τ),
        defaultVal τ = v ↔ Den Θ ρ e v) := by
  intro h
  exact den_is_not_total Θ ((h Env.nil (PE.lit .bool true) false).mp rfl)

/-- The general statement behind it: ANY candidate evaluator that differs from
`evalPE` at a single point fails the row. Together with
`adequacy_pins_the_relation` (§1), the row pins BOTH sides. -/
theorem a_wrong_evaluator_fails_adequacy (Θ : AtomTable)
    (f : {Γ : Ctx} → {τ : VTy} → Env Γ → PE Θ Γ τ → Val τ)
    {Γ : Ctx} {τ : VTy} (ρ : Env Γ) (e : PE Θ Γ τ)
    (hne : f ρ e ≠ evalPE Θ ρ e) :
    ¬ (∀ {Γ : Ctx} {τ : VTy} (ρ : Env Γ) (e : PE Θ Γ τ) (v : Val τ),
        f ρ e = v ↔ Den Θ ρ e v) :=
  fun h => hne (adequacy_pins_the_evaluator Θ f (fun ρ e v => h ρ e v) ρ e)

end Controls

/-! ## §8 — what the row does NOT buy

`ALGEBRA.md` §3 gives a `PureAtom` five clauses. Clauses 1-2 (identity, type,
total Lean meaning) are modeled by `AtomTable`. Clause 3 (a separately
identified TypeScript body) and clause 5 (a conformance obligation between that
body and the Lean meaning) are NOT reachable from this row, and this section
proves it rather than observing it: adequacy is PARAMETRIC in the atom meaning.

`WORKSHOP-RESULTS.md:651` (C9) records clause 5 as PENDING against a pattern
`EFFECTS-BACKEND.md:241` already calls unconfronted on the TypeScript side. This
turns that observation into a theorem: no strengthening of `EC1-T003` reaches
it, so a separate confronting instrument is owed. -/

section AtomOpacity

/-- **The row constrains no host body.** Two atom tables with IDENTICAL
signatures each satisfy `EC1-T003` in full, while the same program denotes
different values under them. So a green `pure_eval_adequate` is compatible with
a TypeScript `PureAtom` body that computes the wrong function, and
`ALGEBRA.md` §3 clause 5 cannot inherit this row. -/
theorem atom_meaning_is_unconstrained :
    (∀ {Γ : Ctx} {τ : VTy} (ρ : Env Γ) (e : PE addTable Γ τ) (v : Val τ),
        evalPE addTable ρ e = v ↔ Den addTable ρ e v)
      ∧ (∀ {Γ : Ctx} {τ : VTy} (ρ : Env Γ) (e : PE mulTable Γ τ) (v : Val τ),
          evalPE mulTable ρ e = v ↔ Den mulTable ρ e v)
      ∧ natOut (evalPE addTable .nil sumFold)
          ≠ natOut (evalPE mulTable .nil mulFold) :=
  ⟨fun ρ e v => pure_eval_adequate addTable ρ e v,
   fun ρ e v => pure_eval_adequate mulTable ρ e v,
   by rw [sumFold_evaluates, mulFold_evaluates]; decide⟩

end AtomOpacity

/-! ## §9 — receipts

Measured ceiling: `[propext]`, and nothing else. Nine of the twenty-eight
theorems depend on no axioms at all. NO `Quot.sound`, NO `Classical.choice`, NO
`sorryAx`, anywhere in this file.

That is below the estate's usual ceiling for this family — `EC1-T003E`'s scout
recorded `[propext, Classical.choice, Quot.sound]` for `Cas.Schema.Ast.WF` and
`EC1-T002`'s recorded the same triple wherever `String`'s order instances are
reached. This carrier touches neither: the only scalars are `Unit`, `Bool` and
`Nat`, whose decidable equality and order are constructive, and `propext`
enters only through `simp`. -/

#print axioms deleted_form_holds_for_every_function
#print axioms adequacy_is_not_a_tautology
#print axioms adequacy_pins_the_relation
#print axioms adequacy_forces_functionality
#print axioms mirror_relation_discharges_the_row
#print axioms resolve_dangles_at_every_env
#print axioms no_unary_env_premise_totalises
#print axioms pin_eval_adequate
#print axioms denFold_of_foldl
#print axioms eval_sound
#print axioms evalArgs_sound
#print axioms eval_complete
#print axioms evalArgs_complete
#print axioms evalFold_complete
#print axioms pure_eval_adequate
#print axioms pure_evalArgs_adequate
#print axioms pure_denotes_deterministic
#print axioms adequacy_pins_the_evaluator
#print axioms premise_free_implies_any_EnvWF
#print axioms caseProj_evaluates
#print axioms caseProj_denotes
#print axioms sumFold_evaluates
#print axioms mulFold_evaluates
#print axioms evalPE_fold
#print axioms den_is_not_total
#print axioms discarding_evaluator_fails_adequacy
#print axioms a_wrong_evaluator_fails_adequacy
#print axioms atom_meaning_is_unconstrained

/-! ## Gate (`lean-algebraic-systems`)

- **Constructor/step equations.** `evalPE`'s fifteen equations plus `evalArgs`'s
  two are the interpreter's step equations; `evalPE_fold` writes the collection
  one out because it is the only arm whose recursion is not syntactic.
- **Interpreter law / adequacy naming observable behavior.**
  `pure_eval_adequate` and `pure_evalArgs_adequate`. The observable is the
  denoted value; the relation is the specification and the evaluator is the
  implementation, and the `iff` is a two-sided refinement, not a one-sided one.
- **Invariant preservation and reachable states.** Carried by the type indices:
  `Var Γ τ` makes an out-of-scope reference unrepresentable and `Env Γ` makes an
  ill-shaped environment unrepresentable, so there is no separate invariant to
  preserve and no `EnvWF` to assume. That is the whole of §2's finding.
- **Trace/replay, idempotence, ordering, merge.** Not applicable and
  deliberately so: `ALGEBRA.md` §3 clause 4 requires a pure atom to read and
  write no effect world, so there is no state, no trace, and no ordering
  obligation. R14a P1 is the same rule from the other side.
- **Environment assumptions, stated.** Exactly one external assumption exists:
  that `Θ.meaning` agrees with the separately identified host body. §8 proves
  this row cannot discharge it. There are no fairness, delivery, failure or
  resource assumptions, because there is nothing here that can fail.
- **Positive scenarios and deliberately invalid programs.** §7. The invalid
  cases are `den_is_not_total` (a value the syntax refuses) and the discarding
  interpreter, which the row rejects.

## Checks omitted, stated

1. **This is a MODEL, not the packet's carrier.** `EC1-D001/D002/D012/D013` do
   not exist; `PROOF-DAG.md` §17 conditions 1 and 13 are OPEN. Every theorem
   here is about the declarations in this file. It is not assurance about a
   `ValueTy` that has not been ruled, and it does not close row `EC1-T003`.
2. `VTy` covers unit/bool/nat/product/sum/list. `EC1-A01`'s proposed
   u8/u32/bytes/addr32/option/schema/service arms are absent, and I did not
   check whether the structural evaluator survives them. I expect it does — no
   arm above depends on the scalar set — but I did not measure it.
3. Records are modeled as iterated products. Named-field records with a row
   discipline were NOT modeled, and `EC1-T001`/`EC1-T002`'s duplicate-key
   obstruction (`EC1-CE030`) would bear on them if they were.
4. `EC1-T003E value_el_bridge` is untouched — a separate row. I did not check
   that `Cas.Schema.El`'s supported overlap can carry this `Val`.
5. The atom table is TOTAL at every `Nat` id (`sig : Nat → AtomSig`). Pinning
   one signature per declared id, and refusing undeclared ids, is
   `EC1-T004`'s obligation, not this row's; modeling it here would have
   imported that row's unresolved carrier question.
6. `fold` is the only collection operation. Map/filter/zip are derivable from it
   at this carrier but were not written, and I did not check that a
   `PureExpr`-level `map` returning a different element type folds cleanly.
7. I ran only `lake env lean` on this file. I did not run `lake build` on
   `library/cas` or `formal/effect-core-v1`, and I wrote nothing under
   `library/`, `formal/`, or any packet `.md`.
8. `EC1-CE030`, `EC1-CE031`, `EC1-CE032` were re-read and do not bear on this
   row. `EC1-CE033` bears on the REPAIR, not the statement: its ruled
   consequence (R15 — restrict the domain by a validity judgment rather than
   assert a premise on one argument) is exactly what §2 and §3 do. No
   `VERIFIED-KERNEL` register row refutes anything proved here.
-/

end EC1T003
