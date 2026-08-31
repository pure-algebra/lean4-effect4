import Cas.Core.Canonicalize

/-!
# `EC1-T006` — `normalizeRaw` is idempotent, because its ladder is coherent

Slice `EC1-S1`, row `EC1-T006`. DAG schematic signature (`PROOF-DAG.md:198`):

```text
EC1-T006 | PENDING THEOREM | normalizeRaw (normalizeRaw r) = normalizeRaw r | D2
```

Run it:

```
cd library/cas
lake env lean ../../.staging/effect-core-v1/workshop/s1/T006.lean
```

Skill stage followed: `lean-model-invariants`. This row is a representation
question in that stage's exact vocabulary — a raw carrier, a normalization
into canonical form, and the fixed-point subtype the checked carrier will be.
The stage's "name obligations before implementation" list is what §6–§8 pay:
*normalization soundness and idempotence*, *preservation by each public
transition*, and *witnesses for valid states and negative examples for invalid
ones*. Its "build visible boundaries" default is `raw -> normalize -> checked`,
and §5's `isCanon_iff` is the boundary predicate.

## What is proved here, and what it is NOT

`EC1-D020 RawProgram` and `EC1-D026 normalizeRaw` are PROPOSED TERMs. Verified
this session: `grep -rn "RawProgram\|normalizeRaw" library formal --include='*.lean'`
returns ZERO hits, and `formal/effect-core-v1/EffectCore/Syntax/Raw.lean` is a
297-byte docstring stub with an empty `namespace EffectCore.Syntax`. So the
carrier below is declared HERE, minimally and first-order. **A green check is
assurance about THESE declarations and nothing else.** It does not close the
DAG row, it is not assurance about the eleven-field `RawProgram` of
`ALGEBRA.md:224-235`, and it prejudges no §17 freeze condition.

Three deliberate departures from the schematic row, each forced and each
proved below rather than argued:

1. **The equation is a `Cas.Canonicalizer` FIELD, not a fresh theorem.**
   `Cas/Core/Canonicalize.lean:53-55` declares
   `canon_idem : ∀ a, canon (canon a) = canon a` as field 2 of the ratified
   `Cas.Canonicalizer` structure. That IS `EC1-T006`, verbatim, already
   admitted at the estate's altitude. §4 packages the two stages through it
   and `normalizeRaw_idempotent` is a projection (`normalizeRawM.canon_idem`),
   not an argument. Proving it standalone would re-mint an existing estate
   abstraction and forfeit `IsCanon`, `Equiv`, the decidable quotient and
   `formAddress` — reuse, never mint.

2. **`normalizeRaw` is a LADDER, and the row is FALSE for the same two stages
   in the other order.** Every anchor in the estate's idempotence family is
   SINGLE-STAGE (`canonServices_idem`, `canonValue_idem`, `canonR_idem`,
   `Value.numNorm_idem`, `deNumNorm_idem`), so `EC1-T006` inherits nothing
   from them. §5 proves at this carrier that two idempotent stages need not
   compose to an idempotent normalizer, that the missing premise is exactly
   `Cas.Canonicalizer.Coherent` (`Canonicalize.lean:155`), and that stage
   ORDER decides the row. `comp` (`:160`) then discharges idempotence for
   free — its own docstring says "Idempotence is inherited, not re-proved per
   ladder." **The reviewable obligation is `normalizeRaw_ladder_coherent`
   plus a frozen stage order, neither of which the DAG row can express.**

3. **The bare equation is HOLLOW, so it does not travel alone.** §6 exhibits
   two distinct functions on this carrier both satisfying the row — the real
   normalizer and `fun _ => empty`. `library/cas/Cas/Backend/Canon.lean:199-214`
   records exactly this hole in the estate's own voice at the keyed-row
   carrier and closes it with preservation laws. §6 supplies the raw-carrier
   analogues (permutation, length, membership, sortedness, alias discharge)
   and proves the discarding normalizer fails them.

**No premise is added to the equation itself.** `EC1-CE030` forces a
duplicate-free premise onto `EC1-T002`'s permutation row; it does not reach an
idempotence row, and `scout-T001.lean`'s `ce030_does_not_reach_t001` already
proved that at the shipped carrier. `normalizeRaw_idempotent` below is
premise-free, exactly as the DAG writes it.

## Which normalizer this is, and the ruling it obeys

`CONTRACT-PACKET.md:320-323` rules: "Checked row normalization is canonical
only under duplicate-free keys... **Raw duplicate-key permutations are
diagnostics, not a normalization equivalence.**" `EC1-F82` is the paired
falsifier: "Permute a duplicate-key raw row and assert equal normalization."

So the raw sort here is STABLE and does NOT deduplicate — unlike the estate's
`canonServices`, which is `dedupLastWins ∘ mergeSort` and is a CHECKED-side
method. §7 proves this normalizer separates a duplicate-key permutation pair,
i.e. it does not supply the equivalence `EC1-F82` attacks. A last-wins raw
normalizer would supply it and turn `EC1-F82` red.

The two stages are the ones the packet's own red controls name.
`TYPE-CLOSURE.md:121` requires "canonical IDs" of the `RawProgram` row and
names "alias capture" as its red control, which is stage R;
`Canonicalize.lean:13-15` names the methods a carrier admits — "trivia
erasure, key sorting, name resolution, positional renaming" — and BOTH stages
are on that list. The insertion sort in §2 is
local scratch machinery, not a proposed declaration: `List.mergeSort` is
well-founded recursion and does not reduce in the kernel, a hazard
`Cas/Backend/Canon.lean:347-349` already records, and §5's and §7's witnesses
are decided by evaluation.

## Axiom ceiling — `Classical.choice` is NOT reached

Receipts are `[propext]`, `[propext, Quot.sound]`, or none. `propext` enters
through the `Decidable` machinery behind `decide` and `simp`; `Quot.sound`
through `List.Perm`. **No receipt reaches `Classical.choice`** — unlike
`scout-T001.lean` and `T001.lean`, which inherit it from `canonServices_idem`'s
`String`-ordered `mergeSort`. Nothing here calls a sorting lemma: keys are
`Nat`, whose `Decidable (· ≤ ·)` instance is choice-free, and the sort is
written locally by structural recursion.

No `sorry`, no `axiom`, no `native_decide`, no `#eval` carrying a claim.
Receipts are at the foot, one line per theorem.
-/

namespace EffectCoreT006

open Cas (Canonicalizer)

/-! ## §1 — the carrier

`ALGEBRA.md:224-235` gives `EC1-A11 RawProgram` eleven fields and
`:238-241` states the design law: "Duplicate identifiers, dangling
references, forged region tokens, invalid rows, bad types, illegal back
edges, host-function payloads, and incomplete handlers are deliberately
representable."

Three of the eleven fields are modelled — `blockTable`, `entry`, and a
declared alias map standing for the "canonical names" half of
`TYPE-CLOSURE.md:121`. Three is the smallest number on which the ladder
question is visible: one table to sort, one substitution to resolve, one
scalar the substitution also moves. Everything is first-order data with
`DecidableEq`, per `EFFECTS-BACKEND.md` R14a — no `Prog`, no `Sig`, no
handler, nothing effectful. Duplicate ids and dangling successors are
representable here, as the design law requires. -/

/-- A raw block identifier: "ordinary bounded numbers or canonical names"
(`ALGEBRA.md:238`). -/
abbrev BlockId := Nat

/-- A raw block: its own identifier and the successors it names. Dangling
successors are deliberately representable. -/
structure RawBlock where
  id : BlockId
  succ : List BlockId
deriving DecidableEq, Repr

/-- The raw carrier. `aliases` is the declared identifier alias map — the
"alias capture" red control of `TYPE-CLOSURE.md:121` made representable, and
the input stage R consumes. `blockTable` is `ALGEBRA.md:234`'s "finite
BlockId -> RawBlock map" as an ordered association list, so duplicate
identifiers and row order are both representable. -/
structure RawProgram where
  aliases : List (BlockId × BlockId)
  blockTable : List RawBlock
  entry : BlockId
deriving DecidableEq, Repr

/-! ## §2 — stage S: canonical key ordering

The sort is STABLE and does NOT deduplicate, because `CONTRACT-PACKET.md:323`
forbids a raw normalization equivalence on duplicate-key permutations. §7
proves the consequence. -/

/-- Insert into a key-ordered list, before the first strictly larger key and
before equal keys reached later in the fold — the placement that makes
`sortBlocks` stable. -/
def insertBlock (b : RawBlock) : List RawBlock → List RawBlock
  | [] => [b]
  | c :: cs => if b.id ≤ c.id then b :: c :: cs else c :: insertBlock b cs

/-- Stable insertion sort by block identifier. No deduplication. -/
def sortBlocks : List RawBlock → List RawBlock
  | [] => []
  | b :: bs => insertBlock b (sortBlocks bs)

/-- The canonical-form predicate for a block table: keys weakly ascending. -/
def KeySorted (xs : List RawBlock) : Prop :=
  xs.Pairwise (fun a b => a.id ≤ b.id)

theorem mem_insertBlock {b c : RawBlock} :
    ∀ {xs : List RawBlock}, c ∈ insertBlock b xs ↔ c = b ∨ c ∈ xs := by
  intro xs
  induction xs with
  | nil => simp [insertBlock]
  | cons d ds ih =>
    by_cases h : b.id ≤ d.id
    · simp [insertBlock, h]
    · have e : insertBlock b (d :: ds) = d :: insertBlock b ds := by
        simp [insertBlock, h]
      rw [e]
      constructor
      · intro hm
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact Or.inr List.mem_cons_self
        · rcases ih.mp hm' with rfl | hm''
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ hm'')
      · rintro (rfl | hm)
        · exact List.mem_cons_of_mem _ (ih.mpr (Or.inl rfl))
        · rcases List.mem_cons.mp hm with rfl | hm'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih.mpr (Or.inr hm'))

theorem insertBlock_perm (b : RawBlock) :
    ∀ xs : List RawBlock, (insertBlock b xs).Perm (b :: xs) := by
  intro xs
  induction xs with
  | nil => exact List.Perm.refl _
  | cons c cs ih =>
    by_cases h : b.id ≤ c.id
    · simp only [insertBlock, h, if_true]
      exact List.Perm.refl _
    · simp only [insertBlock, h, if_false]
      exact (List.Perm.cons c ih).trans (List.Perm.swap b c cs)

theorem sortBlocks_perm : ∀ xs : List RawBlock, (sortBlocks xs).Perm xs := by
  intro xs
  induction xs with
  | nil => exact List.Perm.refl _
  | cons b bs ih =>
    exact (insertBlock_perm b (sortBlocks bs)).trans (List.Perm.cons b ih)

theorem mem_sortBlocks {b : RawBlock} {xs : List RawBlock} :
    b ∈ sortBlocks xs ↔ b ∈ xs :=
  (sortBlocks_perm xs).mem_iff

theorem insertBlock_keySorted {b : RawBlock} :
    ∀ {xs : List RawBlock}, KeySorted xs → KeySorted (insertBlock b xs) := by
  intro xs
  induction xs with
  | nil => intro _; simp [insertBlock, KeySorted]
  | cons c cs ih =>
    intro hs
    rcases List.pairwise_cons.mp hs with ⟨hc, hcs⟩
    by_cases h : b.id ≤ c.id
    · simp only [insertBlock, h, if_true, KeySorted]
      refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨hc, hcs⟩⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact h
      · exact Nat.le_trans h (hc a ha')
    · simp only [insertBlock, h, if_false, KeySorted]
      refine List.pairwise_cons.mpr ⟨?_, ih hcs⟩
      intro a ha
      rcases mem_insertBlock.mp ha with rfl | ha'
      · exact Nat.le_of_not_le h
      · exact hc a ha'

theorem sortBlocks_keySorted : ∀ xs : List RawBlock, KeySorted (sortBlocks xs) := by
  intro xs
  induction xs with
  | nil => simp [sortBlocks, KeySorted]
  | cons b bs ih => exact insertBlock_keySorted ih

theorem insertBlock_of_le {b : RawBlock} :
    ∀ {xs : List RawBlock}, (∀ c ∈ xs, b.id ≤ c.id) → insertBlock b xs = b :: xs := by
  intro xs
  cases xs with
  | nil => intro _; rfl
  | cons c cs =>
    intro h
    have hc : b.id ≤ c.id := h c List.mem_cons_self
    simp only [insertBlock, if_pos hc]

theorem sortBlocks_of_keySorted :
    ∀ {xs : List RawBlock}, KeySorted xs → sortBlocks xs = xs := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro hs
    rcases List.pairwise_cons.mp hs with ⟨hb, hbs⟩
    show insertBlock b (sortBlocks bs) = b :: bs
    rw [ih hbs]
    exact insertBlock_of_le hb

/-- Stage S is idempotent: sorting a sorted table is the identity. -/
theorem sortBlocks_idem (xs : List RawBlock) :
    sortBlocks (sortBlocks xs) = sortBlocks xs :=
  sortBlocks_of_keySorted (sortBlocks_keySorted xs)

/-- Stage S at the program. -/
def sortRaw (r : RawProgram) : RawProgram :=
  { r with blockTable := sortBlocks r.blockTable }

theorem sortRaw_idem (r : RawProgram) : sortRaw (sortRaw r) = sortRaw r := by
  simp [sortRaw, sortBlocks_idem]

/-! ## §3 — stage R: identifier resolution

`TYPE-CLOSURE.md:121` requires "canonical IDs" of the `RawProgram` row and
names "alias capture" as its red control, so `normalizeRaw` owes a resolution
stage. Resolution rewrites every identifier occurrence — block keys, successor
references, and the entry — through the declared alias map, and then discharges
the map: after the pass there are no aliases left to apply. That discharge is
what makes stage R idempotent, and it is also why §5's coherence proof is two
lines. -/

/-- Resolve one identifier through the declared alias map. -/
def resolveId (m : List (BlockId × BlockId)) (i : BlockId) : BlockId :=
  match m.find? (fun p => p.1 == i) with
  | some p => p.2
  | none => i

/-- Resolve every identifier occurring in a block. -/
def resolveBlock (m : List (BlockId × BlockId)) (b : RawBlock) : RawBlock :=
  { id := resolveId m b.id, succ := b.succ.map (resolveId m) }

/-- Stage R at the program: resolve every occurrence, then discharge the map. -/
def resolveRaw (r : RawProgram) : RawProgram :=
  { aliases := []
    blockTable := r.blockTable.map (resolveBlock r.aliases)
    entry := resolveId r.aliases r.entry }

@[simp] theorem resolveId_nil (i : BlockId) : resolveId [] i = i := rfl

@[simp] theorem resolveBlock_nil (b : RawBlock) : resolveBlock [] b = b := by
  have h : ∀ xs : List BlockId, xs.map (resolveId []) = xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a as ih => simp [ih]
  cases b with
  | mk id succ => simp [resolveBlock, h]

theorem map_resolveBlock_nil (xs : List RawBlock) :
    xs.map (resolveBlock []) = xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- A program with a discharged alias map is a fixed point of stage R. -/
theorem resolveRaw_of_aliases_nil {r : RawProgram} (h : r.aliases = []) :
    resolveRaw r = r := by
  cases r with
  | mk aliases blockTable entry =>
    subst h
    simp [resolveRaw, map_resolveBlock_nil]

@[simp] theorem resolveRaw_aliases (r : RawProgram) : (resolveRaw r).aliases = [] := rfl

/-- Stage R is idempotent. -/
theorem resolveRaw_idem (r : RawProgram) : resolveRaw (resolveRaw r) = resolveRaw r :=
  resolveRaw_of_aliases_nil (resolveRaw_aliases r)

/-! ## §4 — the ladder, and `EC1-T006`

`Cas/Core/Canonicalize.lean:155` declares

```lean
def Coherent (c₂ c₁ : Canonicalizer α) : Prop :=
  ∀ a, c₁.canon (c₂.canon (c₁.canon a)) = c₂.canon (c₁.canon a)
```

and `:160` `comp`, whose docstring reads "Idempotence is inherited, not
re-proved per ladder." That is `EC1-T006`, already discharged for any ladder
that supplies the premise. §5 exhibits the pair that does not. -/

/-- Stage R, packaged as the estate's method. -/
def resolveIds : Canonicalizer RawProgram := ⟨resolveRaw, resolveRaw_idem⟩

/-- Stage S, packaged as the estate's method. -/
def sortTables : Canonicalizer RawProgram := ⟨sortRaw, sortRaw_idem⟩

/-- **THE REVIEWABLE OBLIGATION.** The ladder is coherent IN THIS ORDER: the
sort fixes the resolved form, because sorting permutes rows without touching
the discharged alias map, and stage R is the identity once the map is
discharged. This premise — not the equation — is what `EC1-T006` actually
owes, and §5 proves it fails in the other order. -/
theorem normalizeRaw_ladder_coherent : sortTables.Coherent resolveIds := by
  intro r
  exact resolveRaw_of_aliases_nil (by rfl)

/-- `EC1-D026 normalizeRaw`, CONSTRUCTED through the ratified method rather
than asserted: resolve identifiers, then order the tables. -/
def normalizeRawM : Canonicalizer RawProgram :=
  Canonicalizer.comp sortTables resolveIds normalizeRaw_ladder_coherent

/-- `EC1-D026`, as a plain function. -/
def normalizeRaw (r : RawProgram) : RawProgram := normalizeRawM.canon r

/-- The ladder we meant: `comp_canon` says the packaged method runs resolution
and then the sort. -/
theorem normalizeRaw_eq (r : RawProgram) :
    normalizeRaw r = sortRaw (resolveRaw r) := rfl

/-- **`EC1-T006`, as the DAG writes it.** A projection of the `canon_idem`
field of `Cas.Canonicalizer`, not a fresh argument. Premise-free: `EC1-CE030`
does not reach an idempotence row. -/
theorem normalizeRaw_idempotent (r : RawProgram) :
    normalizeRaw (normalizeRaw r) = normalizeRaw r :=
  normalizeRawM.canon_idem r

/-- The retraction form, free from the same package: every normalized program
is a fixed point of the method. This is the shape `CONTRACT-PACKET.md:309`'s
fourth `EC1-K10` equation (`erase checked = normalizeRaw (erase checked)`)
needs. -/
theorem normalizeRaw_isCanon (r : RawProgram) :
    normalizeRawM.IsCanon (normalizeRaw r) :=
  Canonicalizer.isCanon_canon normalizeRawM r

/-- And the conditional form of that equation, stated honestly: any erasure
landing in the method's image satisfies `EC1-K10`'s fourth equation. Whether
`erase` does land there is a D3 obligation this row cannot discharge. -/
theorem k10_fourth_equation_of_erasures_in_the_image
    {Checked : Type} (erase : Checked → RawProgram)
    (h : ∀ p, ∃ r, erase p = normalizeRaw r) (p : Checked) :
    erase p = normalizeRaw (erase p) := by
  obtain ⟨r, hr⟩ := h p
  rw [hr]
  exact (normalizeRaw_idempotent r).symm

/-! ## §5 — the obstruction: stage ORDER decides the row

`EC1-T001`'s anchors are all single-stage, so the estate has never had to
state this. `normalizeRaw` is the first proposed normalizer that is a ladder,
and it inherits nothing from them. -/

/-- The ladder in the order a naive `normalizeRaw` would run it. -/
def sortThenResolve (r : RawProgram) : RawProgram := resolveRaw (sortRaw r)

/-- The witness. One declared alias, `0 ↦ 5`, over an already-sorted two-row
block table. Resolution changes a sort key, so the sort has to run again. -/
def orderWitness : RawProgram :=
  { aliases := [(0, 5)]
    blockTable := [⟨0, []⟩, ⟨1, []⟩]
    entry := 0 }

/-- **Positive control.** Both stages actually fire on the witness: resolution
rewrites the declared alias `0 ↦ 5` in the block key and in the entry, and the
sort then re-orders the table resolution left unsorted. Without this control
every negative result below could be a statement about a normalizer that does
nothing. -/
theorem normalizeRaw_orderWitness :
    normalizeRaw orderWitness = ⟨[], [⟨1, []⟩, ⟨5, []⟩], 5⟩ := by
  decide

/-- **THE OBSTRUCTION.** Both stages are idempotent (`resolveRaw_idem`,
`sortRaw_idem`); their composite in this order is not. The row is FALSE for
this `normalizeRaw`. -/
theorem sortThenResolve_not_idem :
    sortThenResolve (sortThenResolve orderWitness) ≠ sortThenResolve orderWitness := by
  decide

/-- The failure is precisely a failure of ladder coherence: sorting does NOT
fix the resolved form when resolution runs second. -/
theorem ladder_incoherent_in_the_other_order :
    ¬ resolveIds.Coherent sortTables :=
  fun h => absurd (h orderWitness) (by decide)

/-- The finding in `EC1-T006`'s own shape, at `EC1-T006`'s own carrier:
componentwise idempotence does not discharge the row. -/
theorem componentwise_idempotence_is_not_enough :
    ∃ f g : RawProgram → RawProgram,
      (∀ r, f (f r) = f r) ∧ (∀ r, g (g r) = g r) ∧
      ¬ (∀ r, f (g (f (g r))) = f (g r)) :=
  ⟨resolveRaw, sortRaw, resolveRaw_idem, sortRaw_idem,
    fun h => sortThenResolve_not_idem (h orderWitness)⟩

/-- The separation in one statement: the same two stages, one order satisfying
`EC1-T006` and the other refuting it. **A frozen stage order is therefore part
of `EC1-D026`, not an implementation detail.** -/
theorem order_decides_t006 :
    (∀ r, normalizeRaw (normalizeRaw r) = normalizeRaw r)
      ∧ sortThenResolve (sortThenResolve orderWitness) ≠ sortThenResolve orderWitness :=
  ⟨normalizeRaw_idempotent, sortThenResolve_not_idem⟩

/-- The row escapes `PROOF-DAG.md:203-204`'s deleted family: it is not a
tautology for every Lean function, because an endofunction on this very
carrier refutes it. -/
theorem t006_is_not_a_tautology :
    ∃ f : RawProgram → RawProgram, ¬ (∀ r, f (f r) = f r) :=
  ⟨sortThenResolve, fun h => sortThenResolve_not_idem (h orderWitness)⟩

/-! ## §6 — the bare row is hollow, and the preservation bundle that fixes it

`Cas/Backend/Canon.lean:199-214` records this hole in the estate's own voice
at the keyed-row carrier: "Sortedness, distinct keys, idempotence and
order-blindness are all satisfied by a canonicalizer that THROWS SERVICES
AWAY... that is the adequacy hole this section closes." `Canon.lean` closes it
with preservation laws at `:259/:266/:278/:288`. `EC1-T006` imports the
idempotence conjunct and leaves them behind. -/

/-- The discarding normalizer. -/
def discardRaw (_ : RawProgram) : RawProgram := ⟨[], [], 0⟩

theorem discardRaw_idem (r : RawProgram) : discardRaw (discardRaw r) = discardRaw r := rfl

/-- **ADEQUACY-HOLLOW.** Two distinct functions on this carrier both satisfy
`EC1-T006`. The row does not pin `normalizeRaw`. -/
theorem t006_does_not_pin_normalizeRaw :
    ∃ f g : RawProgram → RawProgram,
      (∀ r, f (f r) = f r) ∧ (∀ r, g (g r) = g r) ∧ f ≠ g :=
  ⟨normalizeRaw, discardRaw, normalizeRaw_idempotent, discardRaw_idem,
    fun h => absurd (congrFun h orderWitness) (by decide)⟩

/-- PRESERVE-exact: the normalized table is a permutation of the resolved
table. No row is dropped, duplicated, or invented. -/
theorem normalizeRaw_blockTable_perm (r : RawProgram) :
    (normalizeRaw r).blockTable.Perm (r.blockTable.map (resolveBlock r.aliases)) :=
  sortBlocks_perm _

/-- PRESERVE-count, the conjunct the discarding normalizer fails. -/
theorem normalizeRaw_length (r : RawProgram) :
    (normalizeRaw r).blockTable.length = r.blockTable.length := by
  have h := (normalizeRaw_blockTable_perm r).length_eq
  simpa using h

/-- PRESERVE-elements: membership in the normalized table is membership in the
resolved image of the raw table, both ways. -/
theorem mem_normalizeRaw {r : RawProgram} {b : RawBlock} :
    b ∈ (normalizeRaw r).blockTable ↔ ∃ c ∈ r.blockTable, resolveBlock r.aliases c = b := by
  have h := (normalizeRaw_blockTable_perm r).mem_iff (a := b)
  simpa using h

/-- What the method BUYS, half one: the output is key-ordered. -/
theorem normalizeRaw_keySorted (r : RawProgram) :
    KeySorted (normalizeRaw r).blockTable :=
  sortBlocks_keySorted _

/-- What the method BUYS, half two: the alias map is discharged, so no alias
capture survives normalization. -/
theorem normalizeRaw_aliases_nil (r : RawProgram) : (normalizeRaw r).aliases = [] := rfl

/-- The bundle is not vacuous: the discarding normalizer fails PRESERVE-count. -/
theorem discardRaw_fails_preservation :
    ¬ (∀ r : RawProgram, (discardRaw r).blockTable.length = r.blockTable.length) :=
  fun h => absurd (h orderWitness) (by decide)

/-- **The canonical carrier, characterized.** The method's fixed points are
exactly the alias-discharged, key-ordered programs — so the checked-side
carrier is the subtype `{ r // normalizeRawM.IsCanon r }` and needs no second
type. This is what packaging through `Cas.Canonicalizer` buys that a
standalone `EC1-T006` would not. -/
theorem isCanon_iff (r : RawProgram) :
    normalizeRawM.IsCanon r ↔ (r.aliases = [] ∧ KeySorted r.blockTable) := by
  constructor
  · intro h
    have h' : sortRaw (resolveRaw r) = r := h
    constructor
    · rw [← h']; rfl
    · rw [← h']; exact normalizeRaw_keySorted r
  · rintro ⟨ha, hs⟩
    show sortRaw (resolveRaw r) = r
    rw [resolveRaw_of_aliases_nil ha]
    cases r with
    | mk aliases blockTable entry =>
      simp [sortRaw, sortBlocks_of_keySorted hs]

/-! ## §7 — `EC1-F82`: raw duplicate-key permutations stay diagnostics

`CONTRACT-PACKET.md:320-323` rules that raw duplicate-key permutations are
"diagnostics, not a normalization equivalence", and `EC1-F82` (`:745`) is the
falsifier: "Permute a duplicate-key raw row and assert equal normalization."
The theorem below discharges that obligation for THIS normalizer — a
permutation theorem does not apply, because the stable no-dedup sort keeps the
two presentations apart. A last-wins raw normalizer would supply the forbidden
equivalence. -/

/-- One block identifier written twice, with different successors. -/
def dupA : RawProgram := ⟨[], [⟨0, [1]⟩, ⟨0, [2]⟩], 0⟩

/-- The same two rows, permuted. -/
def dupB : RawProgram := ⟨[], [⟨0, [2]⟩, ⟨0, [1]⟩], 0⟩

/-- Each presentation is its own normal form: the stable sort leaves rows with
equal keys in the order the serialization carried them, and no deduplication
runs. This is the mechanism, stated separately from the consequence. -/
theorem normalizeRaw_dupA : normalizeRaw dupA = dupA := by decide

theorem normalizeRaw_dupB : normalizeRaw dupB = dupB := by decide

theorem dup_is_a_permutation : dupA.blockTable.Perm dupB.blockTable := by
  show (([⟨0, [1]⟩, ⟨0, [2]⟩] : List RawBlock)).Perm [⟨0, [2]⟩, ⟨0, [1]⟩]
  exact List.Perm.swap _ _ _

/-- **`EC1-F82` discharged for this normalizer.** The tables are a permutation
of each other and their normal forms differ, so no raw permutation theorem
applies and admission still sees two distinct duplicate-key programs to
reject. -/
theorem normalizeRaw_separates_duplicate_key_permutations :
    dupA.blockTable.Perm dupB.blockTable ∧ normalizeRaw dupA ≠ normalizeRaw dupB :=
  ⟨dup_is_a_permutation, by decide⟩

/-! ## §8 — `EC1-T006` carries neither composite obligation

`Cas/Schema/Basis.lean:432` (`canonValue_numNorm_comm`, the stages commute)
and `:612` (`normalizers_are_independent`, no stage does another's work) are
the two further theorems the estate proved for its own composite normalizer.
A green `EC1-T006` is no evidence for either. -/

/-- The two stages do not commute — the coherent order and the incoherent one
are different functions. -/
theorem stages_do_not_commute :
    (fun r => sortRaw (resolveRaw r)) ≠ (fun r => resolveRaw (sortRaw r)) :=
  fun h => absurd (congrFun h orderWitness) (by decide)

/-- **The gap finding.** `EC1-T006` holds of the coherent ladder while its two
stages provably do not commute, so `Basis.lean:432/:612` remain separate
obligations that this row does not import. -/
theorem t006_does_not_imply_commutation :
    (∀ r, normalizeRaw (normalizeRaw r) = normalizeRaw r)
      ∧ (fun r => sortRaw (resolveRaw r)) ≠ (fun r => resolveRaw (sortRaw r)) :=
  ⟨normalizeRaw_idempotent, stages_do_not_commute⟩

end EffectCoreT006

/-! ## Kernel receipts -/

#print axioms EffectCoreT006.mem_insertBlock
#print axioms EffectCoreT006.insertBlock_perm
#print axioms EffectCoreT006.sortBlocks_perm
#print axioms EffectCoreT006.mem_sortBlocks
#print axioms EffectCoreT006.insertBlock_keySorted
#print axioms EffectCoreT006.sortBlocks_keySorted
#print axioms EffectCoreT006.insertBlock_of_le
#print axioms EffectCoreT006.sortBlocks_of_keySorted
#print axioms EffectCoreT006.sortBlocks_idem
#print axioms EffectCoreT006.sortRaw_idem
#print axioms EffectCoreT006.resolveId_nil
#print axioms EffectCoreT006.resolveBlock_nil
#print axioms EffectCoreT006.map_resolveBlock_nil
#print axioms EffectCoreT006.resolveRaw_of_aliases_nil
#print axioms EffectCoreT006.resolveRaw_aliases
#print axioms EffectCoreT006.resolveRaw_idem
#print axioms EffectCoreT006.normalizeRaw_ladder_coherent
#print axioms EffectCoreT006.normalizeRaw_eq
#print axioms EffectCoreT006.normalizeRaw_idempotent
#print axioms EffectCoreT006.normalizeRaw_isCanon
#print axioms EffectCoreT006.k10_fourth_equation_of_erasures_in_the_image
#print axioms EffectCoreT006.normalizeRaw_orderWitness
#print axioms EffectCoreT006.sortThenResolve_not_idem
#print axioms EffectCoreT006.ladder_incoherent_in_the_other_order
#print axioms EffectCoreT006.componentwise_idempotence_is_not_enough
#print axioms EffectCoreT006.order_decides_t006
#print axioms EffectCoreT006.t006_is_not_a_tautology
#print axioms EffectCoreT006.discardRaw_idem
#print axioms EffectCoreT006.t006_does_not_pin_normalizeRaw
#print axioms EffectCoreT006.normalizeRaw_blockTable_perm
#print axioms EffectCoreT006.normalizeRaw_length
#print axioms EffectCoreT006.mem_normalizeRaw
#print axioms EffectCoreT006.normalizeRaw_keySorted
#print axioms EffectCoreT006.normalizeRaw_aliases_nil
#print axioms EffectCoreT006.discardRaw_fails_preservation
#print axioms EffectCoreT006.isCanon_iff
#print axioms EffectCoreT006.normalizeRaw_dupA
#print axioms EffectCoreT006.normalizeRaw_dupB
#print axioms EffectCoreT006.dup_is_a_permutation
#print axioms EffectCoreT006.normalizeRaw_separates_duplicate_key_permutations
#print axioms EffectCoreT006.stages_do_not_commute
#print axioms EffectCoreT006.t006_does_not_imply_commutation
