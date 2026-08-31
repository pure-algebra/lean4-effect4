import Cas.Core.Canonicalize

/-!
# Breaker attack on `EC1-T006`

Adversarial companion to `T006.lean`. Nothing here is proposed for the library;
every declaration is scratch. Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T006.lean
```

`T006.lean` is not a module in any lake target, so it cannot be imported. §0
RESTATES the engine under attack VERBATIM, with the line of `T006.lean` each
declaration was copied from, so the attacks bite on the same objects.

The DAG row itself (`PROOF-DAG.md:198`) SURVIVES — §1 reproves it. Four
attacks land on what `T006.lean` claims AROUND the row:

- §2 `EC1-F82` HITS. `T006.lean` §7 claims the falsifier is "discharged for
  this normalizer". It is discharged only for an ALIAS-FREE pair. With a live
  alias map, `normalizeRaw` identifies a permuted DUPLICATE-KEY pair, which is
  exactly the equivalence `CONTRACT-PACKET.md:323` forbids.
- §3 the §6 preservation bundle does NOT determine `normalizeRaw`. A second,
  distinct canonicalizer satisfies all five laws VERBATIM, plus §7's
  separation, plus idempotence — and erases the entry point. The estate's own
  adequacy criterion (`Canon.lean:270-272`, "they determine `canonServices`
  uniquely") is therefore not met.
- §4 stage R is itself an ALIAS-CAPTURING substitution, and manufactures
  duplicate block keys from a duplicate-free program. `TYPE-CLOSURE.md:121`
  names "alias capture" as the red control this very stage was introduced to be.
- §5 the "REVIEWABLE OBLIGATION" `normalizeRaw_ladder_coherent` constrains only
  the alias field: every second stage that leaves `aliases = []` alone is
  coherent over `resolveIds`, including one that discards the block table.

No `sorry`, no `axiom`, no `native_decide`, no `#eval`. `#print axioms` on
every theorem, at the foot.
-/

namespace AttackT006

open Cas (Canonicalizer)

/-! ## §0 — the engine under attack, copied verbatim from `T006.lean` -/

/-- `T006.lean:139`. -/
abbrev BlockId := Nat

/-- `T006.lean:143-146`. -/
structure RawBlock where
  id : BlockId
  succ : List BlockId
deriving DecidableEq, Repr

/-- `T006.lean:153-157`. -/
structure RawProgram where
  aliases : List (BlockId × BlockId)
  blockTable : List RawBlock
  entry : BlockId
deriving DecidableEq, Repr

/-- `T006.lean:168-170`. -/
def insertBlock (b : RawBlock) : List RawBlock → List RawBlock
  | [] => [b]
  | c :: cs => if b.id ≤ c.id then b :: c :: cs else c :: insertBlock b cs

/-- `T006.lean:173-175`. -/
def sortBlocks : List RawBlock → List RawBlock
  | [] => []
  | b :: bs => insertBlock b (sortBlocks bs)

/-- `T006.lean:178-179`. -/
def KeySorted (xs : List RawBlock) : Prop :=
  xs.Pairwise (fun a b => a.id ≤ b.id)

/-- `T006.lean:181-203`. -/
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

/-- `T006.lean:205-215`. -/
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

/-- `T006.lean:217-222`. -/
theorem sortBlocks_perm : ∀ xs : List RawBlock, (sortBlocks xs).Perm xs := by
  intro xs
  induction xs with
  | nil => exact List.Perm.refl _
  | cons b bs ih =>
    exact (insertBlock_perm b (sortBlocks bs)).trans (List.Perm.cons b ih)

/-- `T006.lean:228-247`. -/
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

/-- `T006.lean:249-253`. -/
theorem sortBlocks_keySorted : ∀ xs : List RawBlock, KeySorted (sortBlocks xs) := by
  intro xs
  induction xs with
  | nil => simp [sortBlocks, KeySorted]
  | cons b bs ih => exact insertBlock_keySorted ih

/-- `T006.lean:255-263`. -/
theorem insertBlock_of_le {b : RawBlock} :
    ∀ {xs : List RawBlock}, (∀ c ∈ xs, b.id ≤ c.id) → insertBlock b xs = b :: xs := by
  intro xs
  cases xs with
  | nil => intro _; rfl
  | cons c cs =>
    intro h
    have hc : b.id ≤ c.id := h c List.mem_cons_self
    simp only [insertBlock, if_pos hc]

/-- `T006.lean:265-276`. -/
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

/-- `T006.lean:279-281`. -/
theorem sortBlocks_idem (xs : List RawBlock) :
    sortBlocks (sortBlocks xs) = sortBlocks xs :=
  sortBlocks_of_keySorted (sortBlocks_keySorted xs)

/-- `T006.lean:284-285`. -/
def sortRaw (r : RawProgram) : RawProgram :=
  { r with blockTable := sortBlocks r.blockTable }

/-- `T006.lean:287-288`. -/
theorem sortRaw_idem (r : RawProgram) : sortRaw (sortRaw r) = sortRaw r := by
  simp [sortRaw, sortBlocks_idem]

/-- `T006.lean:301-304`. -/
def resolveId (m : List (BlockId × BlockId)) (i : BlockId) : BlockId :=
  match m.find? (fun p => p.1 == i) with
  | some p => p.2
  | none => i

/-- `T006.lean:307-308`. -/
def resolveBlock (m : List (BlockId × BlockId)) (b : RawBlock) : RawBlock :=
  { id := resolveId m b.id, succ := b.succ.map (resolveId m) }

/-- `T006.lean:311-314`. -/
def resolveRaw (r : RawProgram) : RawProgram :=
  { aliases := []
    blockTable := r.blockTable.map (resolveBlock r.aliases)
    entry := resolveId r.aliases r.entry }

/-- `T006.lean:316`. -/
@[simp] theorem resolveId_nil (i : BlockId) : resolveId [] i = i := rfl

/-- `T006.lean:318-325`. -/
@[simp] theorem resolveBlock_nil (b : RawBlock) : resolveBlock [] b = b := by
  have h : ∀ xs : List BlockId, xs.map (resolveId []) = xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a as ih => simp [ih]
  cases b with
  | mk id succ => simp [resolveBlock, h]

/-- `T006.lean:327-331`. -/
theorem map_resolveBlock_nil (xs : List RawBlock) :
    xs.map (resolveBlock []) = xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- `T006.lean:334-339`. -/
theorem resolveRaw_of_aliases_nil {r : RawProgram} (h : r.aliases = []) :
    resolveRaw r = r := by
  cases r with
  | mk aliases blockTable entry =>
    subst h
    simp [resolveRaw, map_resolveBlock_nil]

/-- `T006.lean:341`. -/
@[simp] theorem resolveRaw_aliases (r : RawProgram) : (resolveRaw r).aliases = [] := rfl

/-- `T006.lean:344-345`. -/
theorem resolveRaw_idem (r : RawProgram) : resolveRaw (resolveRaw r) = resolveRaw r :=
  resolveRaw_of_aliases_nil (resolveRaw_aliases r)

/-- `T006.lean:361`. -/
def resolveIds : Canonicalizer RawProgram := ⟨resolveRaw, resolveRaw_idem⟩

/-- `T006.lean:364`. -/
def sortTables : Canonicalizer RawProgram := ⟨sortRaw, sortRaw_idem⟩

/-- `T006.lean:371-373`. -/
theorem normalizeRaw_ladder_coherent : sortTables.Coherent resolveIds := by
  intro r
  exact resolveRaw_of_aliases_nil (by rfl)

/-- `T006.lean:377-378`. -/
def normalizeRawM : Canonicalizer RawProgram :=
  Canonicalizer.comp sortTables resolveIds normalizeRaw_ladder_coherent

/-- `T006.lean:381`. -/
def normalizeRaw (r : RawProgram) : RawProgram := normalizeRawM.canon r

/-- `T006.lean:425-428`. -/
def orderWitness : RawProgram :=
  { aliases := [(0, 5)]
    blockTable := [⟨0, []⟩, ⟨1, []⟩]
    entry := 0 }

/-- `T006.lean:562`. -/
def dupA : RawProgram := ⟨[], [⟨0, [1]⟩, ⟨0, [2]⟩], 0⟩

/-- `T006.lean:565`. -/
def dupB : RawProgram := ⟨[], [⟨0, [2]⟩, ⟨0, [1]⟩], 0⟩

/-! ## §1 — the DAG row itself SURVIVES

`PROOF-DAG.md:198` writes the row as
`normalizeRaw_idempotent : normalizeRaw (normalizeRaw r) = normalizeRaw r`.
Reproved here character-for-character, premise-free, on the same engine. No
quantifier is narrowed and no hypothesis is added. Everything after this
section attacks claims `T006.lean` makes AROUND the row, not the row. -/

/-- The row, reproved. -/
theorem t006_row_survives (r : RawProgram) :
    normalizeRaw (normalizeRaw r) = normalizeRaw r :=
  normalizeRawM.canon_idem r

/-- The engine is the one `T006.lean` built: the ladder runs resolution and
then the sort. -/
theorem ladder_is_resolve_then_sort (r : RawProgram) :
    normalizeRaw r = sortRaw (resolveRaw r) := rfl

/-- Positive control that both stages fire, reproducing
`T006.lean:435-436`'s `normalizeRaw_orderWitness`. Without it every negative
result below could be about a normalizer that does nothing. -/
theorem control_both_stages_fire :
    normalizeRaw orderWitness = ⟨[], [⟨1, []⟩, ⟨5, []⟩], 5⟩ := by decide

/-- Vacuity probe on `T006.lean:404-410`'s `EC1-K10` row: its hypothesis
`∀ p, ∃ r, erase p = normalizeRaw r` is INHABITED, so that conditional is not
vacuous. The probe PASSES — this is evidence, not a finding. -/
theorem k10_hypothesis_is_inhabited :
    ∃ erase : RawProgram → RawProgram, ∀ p, ∃ r, erase p = normalizeRaw r :=
  ⟨normalizeRaw, fun p => ⟨p, rfl⟩⟩

/-- Second inhabitation, on a genuine checked-side subtype rather than on
`normalizeRaw` itself, so the probe is not answered by a degenerate witness. -/
theorem k10_hypothesis_is_inhabited_on_the_subtype :
    ∀ p : { r : RawProgram // normalizeRawM.IsCanon r }, ∃ r, p.val = normalizeRaw r :=
  fun p => ⟨p.val, p.property.symm⟩

/-! ## §2 — `EC1-F82` HITS THIS NORMALIZER

`CONTRACT-PACKET.md:320-323` rules: "Raw duplicate-key permutations are
diagnostics, not a normalization equivalence." `EC1-F82` (`:745`) is the
falsifier: "Permute a duplicate-key raw row and assert equal normalization."

`T006.lean` §7 claims this is "DISCHARGED FOR THIS NORMALIZER" on the strength
of `normalizeRaw_separates_duplicate_key_permutations`, which is a statement
about ONE pair — `dupA`/`dupB`, both with `aliases = []`. Stage R is switched
OFF on that pair. Turn it on and the separation fails.

`dupC`/`dupD` below are duplicate-key raw rows (both rows keyed `0`),
permutations of each other, and `normalizeRaw` sends them to the SAME normal
form. The alias map does the deduplicating work that the stable sort was
chosen to avoid. -/

/-- Two rows under one key, distinguished only by successors that the declared
alias map identifies. -/
def dupC : RawProgram := ⟨[(1, 3), (2, 3)], [⟨0, [1]⟩, ⟨0, [2]⟩], 0⟩

/-- The same two rows, permuted. -/
def dupD : RawProgram := ⟨[(1, 3), (2, 3)], [⟨0, [2]⟩, ⟨0, [1]⟩], 0⟩

/-- The pair really does carry a duplicate key. -/
theorem dupC_has_duplicate_keys : ¬ (dupC.blockTable.map (·.id)).Nodup := by decide

theorem dupD_has_duplicate_keys : ¬ (dupD.blockTable.map (·.id)).Nodup := by decide

/-- The pair really is a permutation. -/
theorem dupCD_is_a_permutation : dupC.blockTable.Perm dupD.blockTable := by
  show (([⟨0, [1]⟩, ⟨0, [2]⟩] : List RawBlock)).Perm [⟨0, [2]⟩, ⟨0, [1]⟩]
  exact List.Perm.swap _ _ _

/-- The two presentations are genuinely DIFFERENT raw programs, so this is not
a permutation of a row with itself. -/
theorem dupC_ne_dupD : dupC ≠ dupD := by decide

/-- **`EC1-F82` LANDS.** A permuted duplicate-key raw pair with EQUAL
normalization. This is the normalization equivalence `CONTRACT-PACKET.md:323`
forbids, supplied by `T006.lean`'s own `normalizeRaw`. -/
theorem f82_normalizeRaw_identifies_a_permuted_duplicate_key_pair :
    normalizeRaw dupC = normalizeRaw dupD := by decide

/-- The finding in one statement: every conjunct `EC1-F82` asks for, satisfied
at once. -/
theorem f82_is_not_discharged :
    (¬ (dupC.blockTable.map (·.id)).Nodup)
      ∧ dupC.blockTable.Perm dupD.blockTable
      ∧ dupC ≠ dupD
      ∧ normalizeRaw dupC = normalizeRaw dupD :=
  ⟨dupC_has_duplicate_keys, dupCD_is_a_permutation, dupC_ne_dupD,
    f82_normalizeRaw_identifies_a_permuted_duplicate_key_pair⟩

/-- Why `T006.lean` §7 missed it: its witness pair has an EMPTY alias map, so
the stage whose alias map does the identifying never runs. -/
theorem t006_s7_witness_switches_stage_R_off :
    dupA.aliases = [] ∧ dupB.aliases = [] := ⟨rfl, rfl⟩

/-- And the separation `T006.lean` §7 does prove still holds — it is true, just
not general. Both facts together are the finding: separation is a property of
the ALIAS-FREE fragment, not of `normalizeRaw`. -/
theorem separation_holds_only_on_the_alias_free_fragment :
    normalizeRaw dupA ≠ normalizeRaw dupB ∧ normalizeRaw dupC = normalizeRaw dupD :=
  ⟨by decide, f82_normalizeRaw_identifies_a_permuted_duplicate_key_pair⟩

/-! ## §3 — the §6 preservation bundle does NOT determine `normalizeRaw`

`Cas/Backend/Canon.lean:199-214` names the adequacy hole, and `:270-272` states
the estate's criterion for closing it: the preservation laws "together with
distinct keys and sortedness **determine `canonServices` uniquely**, which is
what makes the set adequate."

`T006.lean` §6 does not meet that criterion. Its five laws are all stated
relative to the RESOLVED table `r.blockTable.map (resolveBlock r.aliases)`,
never to `r` itself, and there is NO law about the `entry` field at all —
although `entry` is `ALGEBRA.md:235`'s own field, and it is the field
`T006.lean`'s positive control uses to show stage R fires.

`forgetEntry` below satisfies every one of the five laws VERBATIM — same
statement, same `resolveBlock r.aliases` — plus PRESERVE-count against
`discardRaw`, plus §7's duplicate separation, plus `EC1-T006` itself. And it
throws the entry point away. -/

/-- Backward half of `T006.lean:534-537`'s `isCanon_iff`, needed to run the
witness. -/
theorem normalizeRaw_of_canon {r : RawProgram}
    (ha : r.aliases = []) (hs : KeySorted r.blockTable) : normalizeRaw r = r := by
  show sortRaw (resolveRaw r) = r
  rw [resolveRaw_of_aliases_nil ha]
  cases r with
  | mk aliases blockTable entry =>
    simp [sortRaw, sortBlocks_of_keySorted hs]

/-- `T006.lean:513-515`. -/
theorem normalizeRaw_keySorted (r : RawProgram) :
    KeySorted (normalizeRaw r).blockTable :=
  sortBlocks_keySorted _

/-- `T006.lean:500-502`. -/
theorem normalizeRaw_blockTable_perm (r : RawProgram) :
    (normalizeRaw r).blockTable.Perm (r.blockTable.map (resolveBlock r.aliases)) :=
  sortBlocks_perm _

/-- **THE RIVAL.** `normalizeRaw` with the entry point erased. -/
def forgetEntry (r : RawProgram) : RawProgram :=
  ⟨[], (normalizeRaw r).blockTable, 0⟩

/-- The rival is a lawful canonicalizer: it satisfies `EC1-T006`. -/
theorem forgetEntry_idem (r : RawProgram) :
    forgetEntry (forgetEntry r) = forgetEntry r := by
  have h : normalizeRaw (forgetEntry r) = forgetEntry r :=
    normalizeRaw_of_canon rfl (normalizeRaw_keySorted r)
  show (⟨[], (normalizeRaw (forgetEntry r)).blockTable, 0⟩ : RawProgram) = forgetEntry r
  rw [h]
  rfl

/-- So it is a `Cas.Canonicalizer` in its own right, not a bare function. -/
def forgetEntryM : Canonicalizer RawProgram := ⟨forgetEntry, forgetEntry_idem⟩

/-- PRESERVE-exact, VERBATIM from `T006.lean:500-502`. -/
theorem forgetEntry_blockTable_perm (r : RawProgram) :
    (forgetEntry r).blockTable.Perm (r.blockTable.map (resolveBlock r.aliases)) :=
  normalizeRaw_blockTable_perm r

/-- PRESERVE-count, VERBATIM from `T006.lean:505-508`. -/
theorem forgetEntry_length (r : RawProgram) :
    (forgetEntry r).blockTable.length = r.blockTable.length := by
  have h := (forgetEntry_blockTable_perm r).length_eq
  simpa using h

/-- PRESERVE-elements, VERBATIM from `T006.lean:511-514`. -/
theorem mem_forgetEntry {r : RawProgram} {b : RawBlock} :
    b ∈ (forgetEntry r).blockTable ↔ ∃ c ∈ r.blockTable, resolveBlock r.aliases c = b := by
  have h := (forgetEntry_blockTable_perm r).mem_iff (a := b)
  simpa using h

/-- Sortedness, VERBATIM from `T006.lean:517-519`. -/
theorem forgetEntry_keySorted (r : RawProgram) :
    KeySorted (forgetEntry r).blockTable :=
  normalizeRaw_keySorted r

/-- Alias discharge, VERBATIM from `T006.lean:523`. -/
theorem forgetEntry_aliases_nil (r : RawProgram) : (forgetEntry r).aliases = [] := rfl

/-- It also passes §7's duplicate-key separation, so §6 and §7 TOGETHER still
do not exclude it. -/
theorem forgetEntry_separates_duplicate_key_permutations :
    dupA.blockTable.Perm dupB.blockTable ∧ forgetEntry dupA ≠ forgetEntry dupB := by
  refine ⟨?_, by decide⟩
  show (([⟨0, [1]⟩, ⟨0, [2]⟩] : List RawBlock)).Perm [⟨0, [2]⟩, ⟨0, [1]⟩]
  exact List.Perm.swap _ _ _

/-- And it is a DIFFERENT function. -/
theorem forgetEntry_ne_normalizeRaw : forgetEntry ≠ normalizeRaw :=
  fun h => absurd (congrFun h orderWitness) (by decide)

/-- **What the rival costs: `EC1-F01` in normalizer form.** On the very witness
`T006.lean` uses as its positive control, the rival's entry names no block in
its own table — the target block is, in effect, deleted. `normalizeRaw` gets
this right, but no law in §6 says so. -/
theorem forgetEntry_deletes_the_target_block :
    (∃ b ∈ (normalizeRaw orderWitness).blockTable, b.id = (normalizeRaw orderWitness).entry)
      ∧ ¬ (∃ b ∈ (forgetEntry orderWitness).blockTable, b.id = (forgetEntry orderWitness).entry) := by
  constructor
  · decide
  · decide

/-- `T006.lean:511-514`, restated so the missing law can be proved. -/
theorem mem_normalizeRaw {r : RawProgram} {b : RawBlock} :
    b ∈ (normalizeRaw r).blockTable ↔ ∃ c ∈ r.blockTable, resolveBlock r.aliases c = b := by
  have h := (normalizeRaw_blockTable_perm r).mem_iff (a := b)
  simpa using h

/-- **The missing law is an OMISSION, not an impossibility.** `normalizeRaw`
DOES preserve "the entry names a block", and the proof is four lines. §6 simply
never states it, which is why `forgetEntry` slips through the bundle. -/
theorem entry_has_a_block_is_preserved {r : RawProgram}
    (h : ∃ b ∈ r.blockTable, b.id = r.entry) :
    ∃ b ∈ (normalizeRaw r).blockTable, b.id = (normalizeRaw r).entry := by
  obtain ⟨b, hb, hbe⟩ := h
  refine ⟨resolveBlock r.aliases b, mem_normalizeRaw.mpr ⟨b, hb, rfl⟩, ?_⟩
  show resolveId r.aliases b.id = resolveId r.aliases r.entry
  rw [hbe]

/-- And `forgetEntry` refutes that law, which is exactly the gap. -/
theorem forgetEntry_refutes_the_missing_law :
    ¬ (∀ r : RawProgram, (∃ b ∈ r.blockTable, b.id = r.entry) →
        ∃ b ∈ (forgetEntry r).blockTable, b.id = (forgetEntry r).entry) :=
  fun h => absurd (h orderWitness (by decide)) (by decide)

/-- **THE FINDING.** Every law `T006.lean` §6 and §7 prove, satisfied at once by
a function that is not `normalizeRaw`. The bundle does not determine the
normalizer, so `Canon.lean:270-272`'s adequacy criterion is not met and the
adequacy hole `Canon.lean:199-214` names is still open at this carrier. -/
theorem section6_and_7_do_not_determine_normalizeRaw :
    ∃ N : RawProgram → RawProgram,
      (∀ r, N (N r) = N r)
        ∧ (∀ r, (N r).blockTable.Perm (r.blockTable.map (resolveBlock r.aliases)))
        ∧ (∀ r, (N r).blockTable.length = r.blockTable.length)
        ∧ (∀ (r : RawProgram) (b : RawBlock),
            b ∈ (N r).blockTable ↔ ∃ c ∈ r.blockTable, resolveBlock r.aliases c = b)
        ∧ (∀ r, KeySorted (N r).blockTable)
        ∧ (∀ r, (N r).aliases = [])
        ∧ (dupA.blockTable.Perm dupB.blockTable ∧ N dupA ≠ N dupB)
        ∧ N ≠ normalizeRaw :=
  ⟨forgetEntry, forgetEntry_idem, forgetEntry_blockTable_perm, forgetEntry_length,
    fun _ _ => mem_forgetEntry, forgetEntry_keySorted, forgetEntry_aliases_nil,
    forgetEntry_separates_duplicate_key_permutations, forgetEntry_ne_normalizeRaw⟩

/-- The missing law, named: nothing in §6 constrains `entry`, and the two
canonicalizers differ there and only there. -/
theorem the_missing_law_is_about_entry :
    (∀ r : RawProgram, (forgetEntry r).blockTable = (normalizeRaw r).blockTable)
      ∧ (∀ r : RawProgram, (forgetEntry r).aliases = (normalizeRaw r).aliases)
      ∧ (forgetEntry orderWitness).entry ≠ (normalizeRaw orderWitness).entry :=
  ⟨fun _ => rfl, fun _ => rfl, by decide⟩

/-! ## §4 — stage R IS the red control it was introduced to be

`TYPE-CLOSURE.md:121` lists the `RawProgram` row's red controls as "function
field, dangling ID, **alias capture**, delegation cycle, second CAS spelling".
`T006.lean:148-152` introduces the alias map as "the 'alias capture' red
control of `TYPE-CLOSURE.md:121` made representable", and stage R as the pass
that discharges it.

Stage R is a single-step, non-injective, non-capture-avoiding substitution. It
resolves a block INTO a name another block already occupies, and so
manufactures duplicate block keys out of a duplicate-free program. That is
`EC1-F03` ("duplicate a block/operation/handler ID") produced by the
normalizer itself. -/

/-- A duplicate-FREE raw program: keys `0` and `5`, with one declared alias
`0 ↦ 5` pointing the first at the second's name. -/
def captureWitness : RawProgram := ⟨[(0, 5)], [⟨0, [9]⟩, ⟨5, [7]⟩], 0⟩

theorem captureWitness_keys_are_distinct :
    (captureWitness.blockTable.map (·.id)).Nodup := by decide

/-- Resolution walks block `0` into the occupied name `5`. -/
theorem normalizeRaw_captures_an_occupied_name :
    normalizeRaw captureWitness = ⟨[], [⟨5, [9]⟩, ⟨5, [7]⟩], 5⟩ := by decide

/-- **`EC1-F03` FROM INSIDE THE NORMALIZER.** A duplicate-free raw program whose
normal form has duplicate keys. -/
theorem normalizeRaw_manufactures_duplicate_keys :
    ∃ r : RawProgram,
      (r.blockTable.map (·.id)).Nodup
        ∧ ¬ ((normalizeRaw r).blockTable.map (·.id)).Nodup :=
  ⟨captureWitness, captureWitness_keys_are_distinct, by decide⟩

/-- Consequence for the register: `EC1-CE030`'s repair adds a DUPLICATE-FREE
premise. That premise is not preserved by `normalizeRaw`, so the premise cannot
be discharged upstream of normalization and then reused downstream. -/
theorem ce030_premise_is_not_preserved_by_normalizeRaw :
    ∃ r : RawProgram,
      (r.blockTable.map (·.id)).Nodup
        ∧ ¬ ((normalizeRaw r).blockTable.map (·.id)).Nodup :=
  normalizeRaw_manufactures_duplicate_keys

/-- Stage R is not idempotent AS A SUBSTITUTION — only as a program pass,
because it discharges the map. A declared alias survives, unapplied, in the
normal form: the output still names `5`, which the input's own map sends to
`9`. So `TYPE-CLOSURE.md:121`'s "canonical IDs" obligation is NOT met. -/
def chainWitness : RawProgram := ⟨[(0, 5), (5, 9)], [⟨0, []⟩], 0⟩

theorem normalizeRaw_chainWitness :
    normalizeRaw chainWitness = ⟨[], [⟨5, []⟩], 5⟩ := by decide

theorem normalizeRaw_leaves_a_declared_alias_unapplied :
    ∃ r : RawProgram, ∃ b ∈ (normalizeRaw r).blockTable,
      resolveId r.aliases b.id ≠ b.id :=
  ⟨chainWitness, ⟨5, []⟩, by decide, by decide⟩

/-- Two alias maps with the SAME substitution closure (`0 ↦ 9`) give DIFFERENT
normal forms, so `normalizeRaw` does not canonicalize identifiers. This is the
`EC1-T007` (`normalizeRaw_alpha`) direction, refuted for chained maps before it
is attempted. -/
def chainWitness' : RawProgram := ⟨[(0, 9), (5, 9)], [⟨0, []⟩], 0⟩

theorem alias_chains_are_not_canonicalized :
    normalizeRaw chainWitness ≠ normalizeRaw chainWitness' := by decide

/-! ## §5 — the "REVIEWABLE OBLIGATION" constrains only the alias field

`T006.lean:366-370` calls `normalizeRaw_ladder_coherent` "**THE REVIEWABLE
OBLIGATION** ... what `EC1-T006` actually owes". It is a real theorem, but it
is nearly free: because stage R DISCHARGES its map, `resolveIds` is the
identity on its own image, so EVERY second stage that leaves `aliases = []`
alone is coherent over it — including one that discards the block table. The
obligation therefore reviews the alias field and nothing else, and in
particular reviews nothing about the sort. -/

/-- Coherence over `resolveIds` follows from one alias-field condition alone.
Compare `T006.lean:371-373`, which is this lemma at `sortTables`. -/
theorem coherence_over_resolveIds_is_free (c : Canonicalizer RawProgram)
    (h : ∀ r : RawProgram, (c.canon (resolveRaw r)).aliases = []) :
    c.Coherent resolveIds :=
  fun r => resolveRaw_of_aliases_nil (h r)

/-- A second stage that throws the block table away, but keeps the alias field. -/
def crushStage : Canonicalizer RawProgram :=
  ⟨fun r => ⟨r.aliases, [], 0⟩, fun _ => rfl⟩

/-- It clears the obligation. -/
theorem crushStage_coherent : crushStage.Coherent resolveIds :=
  coherence_over_resolveIds_is_free crushStage (fun _ => rfl)

/-- So it builds a lawful ladder through the ratified `comp`. -/
def crushM : Canonicalizer RawProgram :=
  Canonicalizer.comp crushStage resolveIds crushStage_coherent

/-- Which satisfies `EC1-T006`, by the same projection `T006.lean` uses. -/
theorem crushM_satisfies_t006 (r : RawProgram) :
    crushM.canon (crushM.canon r) = crushM.canon r :=
  crushM.canon_idem r

/-- **THE FINDING.** The obligation `T006.lean` elevates as the row's real
content is cleared by a ladder that discards every block. Coherence over
`resolveIds` is a statement about the alias field, not about the ladder. -/
theorem the_coherence_obligation_admits_a_discarding_ladder :
    crushStage.Coherent resolveIds
      ∧ (∀ r : RawProgram, crushM.canon (crushM.canon r) = crushM.canon r)
      ∧ ¬ (∀ r : RawProgram, (crushM.canon r).blockTable.length = r.blockTable.length) :=
  ⟨crushStage_coherent, crushM_satisfies_t006, fun h => absurd (h orderWitness) (by decide)⟩

/-! ## §6 — what SURVIVES

Recorded so the verdict is not read as broader than the evidence. -/

/-- The order obstruction `T006.lean` §5 reports is real: reproved here. -/
def sortThenResolve (r : RawProgram) : RawProgram := resolveRaw (sortRaw r)

theorem order_obstruction_survives :
    sortThenResolve (sortThenResolve orderWitness) ≠ sortThenResolve orderWitness := by
  decide

/-- The fixed-point characterization `T006.lean:530-543` survives: reproved
independently in both directions. -/
theorem isCanon_iff_survives (r : RawProgram) :
    normalizeRawM.IsCanon r ↔ (r.aliases = [] ∧ KeySorted r.blockTable) := by
  constructor
  · intro h
    have h' : sortRaw (resolveRaw r) = r := h
    exact ⟨by rw [← h']; rfl, by rw [← h']; exact normalizeRaw_keySorted r⟩
  · rintro ⟨ha, hs⟩
    exact normalizeRaw_of_canon ha hs

/-- The axiom ceiling claim survives: nothing here or in `T006.lean` reaches
`Classical.choice`, and the receipts at the foot show it. -/
theorem no_choice_needed (r : RawProgram) :
    normalizeRaw (normalizeRaw r) = normalizeRaw r :=
  normalizeRawM.canon_idem r

end AttackT006

/-! ## Kernel receipts

The §0 engine copied verbatim from `T006.lean` comes first, so its receipts can
be compared line-for-line with that file's own. -/

#print axioms AttackT006.mem_insertBlock
#print axioms AttackT006.insertBlock_perm
#print axioms AttackT006.sortBlocks_perm
#print axioms AttackT006.insertBlock_keySorted
#print axioms AttackT006.sortBlocks_keySorted
#print axioms AttackT006.insertBlock_of_le
#print axioms AttackT006.sortBlocks_of_keySorted
#print axioms AttackT006.sortBlocks_idem
#print axioms AttackT006.sortRaw_idem
#print axioms AttackT006.resolveId_nil
#print axioms AttackT006.resolveBlock_nil
#print axioms AttackT006.map_resolveBlock_nil
#print axioms AttackT006.resolveRaw_of_aliases_nil
#print axioms AttackT006.resolveRaw_aliases
#print axioms AttackT006.resolveRaw_idem
#print axioms AttackT006.normalizeRaw_ladder_coherent
#print axioms AttackT006.normalizeRaw_keySorted
#print axioms AttackT006.normalizeRaw_blockTable_perm

#print axioms AttackT006.t006_row_survives
#print axioms AttackT006.ladder_is_resolve_then_sort
#print axioms AttackT006.control_both_stages_fire
#print axioms AttackT006.k10_hypothesis_is_inhabited
#print axioms AttackT006.k10_hypothesis_is_inhabited_on_the_subtype
#print axioms AttackT006.dupC_has_duplicate_keys
#print axioms AttackT006.dupD_has_duplicate_keys
#print axioms AttackT006.dupCD_is_a_permutation
#print axioms AttackT006.dupC_ne_dupD
#print axioms AttackT006.f82_normalizeRaw_identifies_a_permuted_duplicate_key_pair
#print axioms AttackT006.f82_is_not_discharged
#print axioms AttackT006.t006_s7_witness_switches_stage_R_off
#print axioms AttackT006.separation_holds_only_on_the_alias_free_fragment
#print axioms AttackT006.normalizeRaw_of_canon
#print axioms AttackT006.forgetEntry_idem
#print axioms AttackT006.forgetEntry_blockTable_perm
#print axioms AttackT006.forgetEntry_length
#print axioms AttackT006.mem_forgetEntry
#print axioms AttackT006.forgetEntry_keySorted
#print axioms AttackT006.forgetEntry_aliases_nil
#print axioms AttackT006.forgetEntry_separates_duplicate_key_permutations
#print axioms AttackT006.forgetEntry_ne_normalizeRaw
#print axioms AttackT006.forgetEntry_deletes_the_target_block
#print axioms AttackT006.mem_normalizeRaw
#print axioms AttackT006.entry_has_a_block_is_preserved
#print axioms AttackT006.forgetEntry_refutes_the_missing_law
#print axioms AttackT006.section6_and_7_do_not_determine_normalizeRaw
#print axioms AttackT006.the_missing_law_is_about_entry
#print axioms AttackT006.captureWitness_keys_are_distinct
#print axioms AttackT006.normalizeRaw_captures_an_occupied_name
#print axioms AttackT006.normalizeRaw_manufactures_duplicate_keys
#print axioms AttackT006.ce030_premise_is_not_preserved_by_normalizeRaw
#print axioms AttackT006.normalizeRaw_chainWitness
#print axioms AttackT006.normalizeRaw_leaves_a_declared_alias_unapplied
#print axioms AttackT006.alias_chains_are_not_canonicalized
#print axioms AttackT006.coherence_over_resolveIds_is_free
#print axioms AttackT006.crushStage_coherent
#print axioms AttackT006.crushM_satisfies_t006
#print axioms AttackT006.the_coherence_obligation_admits_a_discarding_ladder
#print axioms AttackT006.order_obstruction_survives
#print axioms AttackT006.isCanon_iff_survives
#print axioms AttackT006.no_choice_needed
