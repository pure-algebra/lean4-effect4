import Cas.Core.Canonicalize

/-!
# Effect Core v1 — scout probe for `EC1-T006 normalizeRaw_idempotent`

Row under scout (`PROOF-DAG.md:198`):

```text
EC1-T006 | PENDING THEOREM | normalizeRaw (normalizeRaw r) = normalizeRaw r | D2
```

Run it:

```
cd library/cas
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T006.lean
```

Stage: `lean-formalization-strategy` **Pass A** — no contract exists for
this row. `EC1-D020 RawProgram` and `EC1-D026 normalizeRaw` are PROPOSED
TERMs, and `formal/effect-core-v1/EffectCore/Syntax/Raw.lean` is an empty
stub. Nothing below defines either. Every probe runs at a two-row model
of `RawProgram`'s `blockTable` (`ALGEBRA.md:224-235`), which is the
smallest carrier on which the obstruction is visible.

`scout-T001.lean` already settled, at the shipped keyed-row carrier,
that a bare idempotence row (a) does not pin its normalizer, (b) is the
`canon_idem` FIELD of `Cas.Canonicalizer` rather than a theorem, and
(c) degenerates to `rfl` at a checked carrier. Those findings transfer
unchanged and are NOT reproved here. This file answers only what is NEW
at `T006`'s carrier — that `normalizeRaw` is a MULTI-STAGE normalizer,
which `T001`'s single-stage anchor never was.

| § | Question | Answer |
|---|---|---|
| 1 | Do idempotent stages compose to an idempotent normalizer? | **No.** Counterexample at a two-row block table. |
| 2 | What exactly is the missing premise? | `Cas.Canonicalizer.Coherent`. The estate already owns it and `comp`. |
| 3 | Does stage ORDER decide it? | Yes. Resolve-then-sort is coherent; sort-then-resolve is not. |
| 4 | Is the field-wise route free? | Yes. A product of methods needs no premise. |
| 5 | Does `T006` carry the commutation/independence obligations? | **No.** Coherent stages need not commute. |

`EC1-CE030`–`CE033` are examined in the report, not here: none of them
attacks an idempotence statement, and §1 below is a NEW obstruction that
the register does not yet carry.

Kernel receipts at the foot. No `sorry`, no `axiom`, no `native_decide`,
no `#eval`.

## Axiom ceiling — `Classical.choice` is NOT reached

Eleven of the thirteen receipts report `[propext]`; `S_idem` and
`t006_is_free_field_wise` report none. `propext` enters through the
`Decidable` machinery `decide` runs on `Fin 3` and on the `if` in
`resolve`/`S`. **No receipt reaches `Classical.choice`** — unlike
`scout-T001.lean`, which inherits it from `canonServices_idem`'s
`mergeSort` route. Nothing here calls a sorting lemma: the carrier is
finite and the sort is a two-element swap, so the kernel decides every
claim by evaluation.
-/

namespace EffectCoreScoutT006

open Cas (Canonicalizer)

/-! ## The carrier — a two-row block table

`ALGEBRA.md:224-235` gives `RawProgram` eleven fields, of which
`blockTable` is a "finite BlockId -> RawBlock map". Below is that table
at two rows over three identifiers: `Table` is an ordered pair of
`BlockId`s. Everything is finite, so every law closes by `decide` and no
sorting lemma or classical axiom is reached. -/

/-- A block identifier. -/
abbrev Rid := Fin 3

/-- The table: two rows, in the order the serialization carries them. -/
abbrev Table := Rid × Rid

/-! ### Stage R — alias resolution

`TYPE-CLOSURE.md:121` names "alias capture" as a hazard the raw carrier
must represent, so `normalizeRaw` owes a resolution stage. Here row `0`
is an alias for row `2`. -/

/-- Resolve one identifier through the alias map. -/
def resolve (i : Rid) : Rid := if i = 0 then 2 else i

/-- The stage: resolve every identifier in the table. -/
def R (t : Table) : Table := (resolve t.1, resolve t.2)

/-! ### Stage S — key sort

The `Canonicalize.lean` front page lists "key sorting" first among
methods, and every shipped normalizer in the estate
(`canonServices`, `canonValue`, `canonR`) is one. -/

/-- The stage: put the two rows in identifier order. -/
def S (t : Table) : Table := if t.1 ≤ t.2 then t else (t.2, t.1)

/-! ## §1 — idempotent stages do NOT compose to an idempotent normalizer

This is the obstruction `EC1-T006` does not name. `EC1-T001`'s anchors
are all single-stage (`canonServices_idem`, `canonValue_idem`,
`canonR_idem`, `Value.numNorm_idem`, `deNumNorm_idem`), so the estate
has never had to state it at the row level. `normalizeRaw` is the first
proposed normalizer that is a LADDER. -/

/-- Stage R is idempotent — resolving twice resolves once. -/
theorem R_idem₂ : ∀ x y : Rid, R (R (x, y)) = R (x, y) := by decide

/-- Stage S is idempotent — sorting twice sorts once. -/
theorem S_idem₂ : ∀ x y : Rid, S (S (x, y)) = S (x, y) := by decide

theorem R_idem : ∀ t : Table, R (R t) = R t := fun ⟨x, y⟩ => R_idem₂ x y

theorem S_idem : ∀ t : Table, S (S t) = S t := fun ⟨x, y⟩ => S_idem₂ x y

/-- The ladder in the order a naive `normalizeRaw` would run it: sort
the table, then resolve aliases. -/
def sortThenResolve (t : Table) : Table := R (S t)

/-- **THE OBSTRUCTION.** Both stages are idempotent; their composite is
not. On `(1, 0)` the first pass sorts to `(0, 1)` and resolves to
`(2, 1)`; the second pass sorts THAT to `(1, 2)` and resolves to
`(1, 2)`. Resolution changed the sort key, so the sort had to run
again — and the row's equation is false. -/
theorem sortThenResolve_not_idem :
    sortThenResolve (sortThenResolve (1, 0)) ≠ sortThenResolve (1, 0) := by
  decide

/-- The finding as an existence statement over the carrier, in exactly
the shape `EC1-T006` is written in: componentwise idempotence does not
discharge the row. -/
theorem componentwise_idempotence_is_not_enough :
    ∃ f g : Table → Table,
      (∀ t, f (f t) = f t) ∧ (∀ t, g (g t) = g t) ∧
      ¬ (∀ t, f (g (f (g t))) = f (g t)) :=
  ⟨R, S, R_idem, S_idem, fun h => sortThenResolve_not_idem (h (1, 0))⟩

/-! ## §2 — the missing premise is `Cas.Canonicalizer.Coherent`

`Cas/Core/Canonicalize.lean:155` declares

```lean
def Coherent (c₂ c₁ : Canonicalizer α) : Prop :=
  ∀ a, c₁.canon (c₂.canon (c₁.canon a)) = c₂.canon (c₁.canon a)
```

with `:158-165` `comp`, whose docstring reads "Idempotence is inherited,
not re-proved per ladder." That is `EC1-T006`, already discharged for
any ladder that supplies the premise. §1's pair is exactly the pair that
does not. -/

/-- Stage S, packaged as the estate's method. -/
def sortM : Canonicalizer Table := ⟨S, S_idem⟩

/-- Stage R, packaged as the estate's method. -/
def resolveM : Canonicalizer Table := ⟨R, R_idem⟩

/-- §1's failure is precisely a failure of ladder coherence: sorting
does NOT fix the resolved form. -/
theorem sortThenResolve_is_incoherent : ¬ Canonicalizer.Coherent resolveM sortM :=
  fun h => absurd (h (1, 0)) (by decide)

/-! ## §3 — stage ORDER decides the row

The same two stages in the other order — resolve first, then sort — DO
form a coherent ladder, so `EC1-T006` holds there with no premise left
over. This is the actionable half of the scout: `normalizeRaw`'s stage
order is not a matter of taste, it is what makes or breaks the row. -/

/-- The repaired ladder. -/
def resolveThenSort (t : Table) : Table := S (R t)

/-- The coherence premise holds in this order: resolution fixes the
sorted-and-resolved form. -/
theorem resolveThenSort_coherent : Canonicalizer.Coherent sortM resolveM := by
  rintro ⟨x, y⟩
  revert x y
  decide

/-- **THE REPAIR.** `EC1-T006` for the coherent ladder, obtained as the
`canon_idem` FIELD of `Cas.Canonicalizer.comp` — not proved here, and
not owed by Effect Core v1 at all. -/
def normalizeTable : Canonicalizer Table :=
  Canonicalizer.comp sortM resolveM resolveThenSort_coherent

/-- The row, read off the package. -/
theorem t006_at_the_coherent_ladder (t : Table) :
    normalizeTable.canon (normalizeTable.canon t) = normalizeTable.canon t :=
  normalizeTable.canon_idem t

/-- And it is the ladder we meant: `comp_canon` says the packaged method
runs resolution then the sort. -/
theorem normalizeTable_is_resolveThenSort (t : Table) :
    normalizeTable.canon t = resolveThenSort t := rfl

/-- The order separation, in one statement: one order satisfies
`EC1-T006`, the other refutes it, and the two stages are the same. -/
theorem order_decides_t006 :
    (∀ t, resolveThenSort (resolveThenSort t) = resolveThenSort t) ∧
      sortThenResolve (sortThenResolve (1, 0)) ≠ sortThenResolve (1, 0) :=
  ⟨normalizeTable.canon_idem, sortThenResolve_not_idem⟩

/-! ## §4 — the field-wise route is free

`RawProgram` has eleven fields. If `normalizeRaw` normalizes each field
INDEPENDENTLY — a product of methods, not a ladder — then `EC1-T006` is
congruence and needs no premise at all. The estate ships `comp` but no
product combinator; the one below is a scout probe, not a promotion. -/

/-- The product of two methods. Idempotence is componentwise. -/
def pairM {α β : Type} (a : Canonicalizer α) (b : Canonicalizer β) :
    Canonicalizer (α × β) where
  canon p := (a.canon p.1, b.canon p.2)
  canon_idem := fun ⟨x, y⟩ => by
    show (a.canon (a.canon x), b.canon (b.canon y)) = _
    rw [a.canon_idem, b.canon_idem]

/-- **The cheap route.** A field-wise `normalizeRaw` discharges
`EC1-T006` with no coherence obligation. The design cost is that no
stage may read another field — which is exactly what identifier
renumbering, alias resolution, and dead-block pruning all do. -/
theorem t006_is_free_field_wise {α β : Type}
    (a : Canonicalizer α) (b : Canonicalizer β) (p : α × β) :
    (pairM a b).canon ((pairM a b).canon p) = (pairM a b).canon p :=
  (pairM a b).canon_idem p

/-! ## §5 — `EC1-T006` carries neither the commutation nor the
independence obligation

`2026-08-31-effect-core-local-anchors.md:269` records that the estate's
composite normalizers owe two further theorems — `canonValue_numNorm_comm`
(`Cas/Schema/Basis.lean:432`, the stages commute) and
`normalizers_are_independent` (`:612`, no stage does another's work) —
and that `T006` as one row carries neither. That is provable at this
carrier: the coherent ladder of §3 satisfies `EC1-T006` and its stages
do NOT commute. -/

/-- The two stages do not commute — one order is idempotent, the other
is not, so they are different functions. -/
theorem stages_do_not_commute : resolveThenSort ≠ sortThenResolve := by
  intro h
  exact sortThenResolve_not_idem (by
    have h₁ : sortThenResolve (1, 0) = resolveThenSort (1, 0) := by rw [h]
    have h₂ : sortThenResolve (sortThenResolve (1, 0))
        = resolveThenSort (resolveThenSort (1, 0)) := by rw [h₁, h]
    rw [h₂, h₁]
    exact normalizeTable.canon_idem (1, 0))

/-- **The gap finding.** `EC1-T006` holds of the coherent ladder while
the commutation law fails of the same two stages. A green `T006` is
therefore no evidence that `normalizeRaw`'s stages are independent, and
`Cas/Schema/Basis.lean:432/612` remain separate obligations. -/
theorem t006_does_not_imply_commutation :
    (∀ t, resolveThenSort (resolveThenSort t) = resolveThenSort t) ∧
      resolveThenSort ≠ sortThenResolve :=
  ⟨normalizeTable.canon_idem, stages_do_not_commute⟩

/-! ## §6 — the row has content at this carrier

`PROOF-DAG.md:206-209` deletes two rows as "tautologies for any Lean
function". `EC1-T006` is not one of them: §1 exhibits an endofunction on
the carrier that fails it. The vacuity hazard is the one `scout-T001`
§4 already recorded — a normalizer read as an endomorphism of the
ALREADY-normalized carrier — and it applies here identically. -/

/-- Not a tautology: an endofunction on the very carrier `EC1-T006`
quantifies over that refutes the row. -/
theorem t006_is_not_a_tautology :
    ∃ f : Table → Table, ¬ (∀ t, f (f t) = f t) :=
  ⟨sortThenResolve, fun h => sortThenResolve_not_idem (h (1, 0))⟩

end EffectCoreScoutT006

/-! ## Kernel receipts -/

#print axioms EffectCoreScoutT006.R_idem
#print axioms EffectCoreScoutT006.S_idem
#print axioms EffectCoreScoutT006.sortThenResolve_not_idem
#print axioms EffectCoreScoutT006.componentwise_idempotence_is_not_enough
#print axioms EffectCoreScoutT006.sortThenResolve_is_incoherent
#print axioms EffectCoreScoutT006.resolveThenSort_coherent
#print axioms EffectCoreScoutT006.t006_at_the_coherent_ladder
#print axioms EffectCoreScoutT006.normalizeTable_is_resolveThenSort
#print axioms EffectCoreScoutT006.order_decides_t006
#print axioms EffectCoreScoutT006.t006_is_free_field_wise
#print axioms EffectCoreScoutT006.stages_do_not_commute
#print axioms EffectCoreScoutT006.t006_does_not_imply_commutation
#print axioms EffectCoreScoutT006.t006_is_not_a_tautology
