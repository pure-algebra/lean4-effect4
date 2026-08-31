import Cas.Lang.Defun
import Cas.Lang.RefusalMap

/-!
# Attack witnesses against `EC1-T017` (`checked_aer_exact`), slice `EC1-S2`

BREAKER artifact. Nothing here is proposed for `library/` or for
`formal/effect-core-v1/`, and nothing outside this file was modified. Run from
`library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/attack-T017.lean
```

Skill stage: `.claude/skills/lean/workflows/lean-assurance-review/SKILL.md`.
Findings use its vocabulary. `T017.lean` was rerun first: it exits zero and
prints 55 receipts, one per `theorem` (56 lines match `^theorem`; one is a
doc-comment line reading "theorem table)"), ceiling `[propext, Quot.sound]`. No
`sorry`, `axiom`, `sorryAx`, `native_decide`, `Classical.choice`, or `#eval`
standing in for a proof. The reported count is HONEST — 55 receipts for 55
`theorem` declarations, and the one further `#print axioms` mentioned in the
file (`List.all_eq_false`) is inside a comment, not a claimed receipt.

## Fidelity

`T017.lean`:96-1020 is re-included VERBATIM below (`namespace EC1T017` through
`end EC1T017`, byte-identical, `diff`-checked) so that this file runs under the
plain command with no `LEAN_PATH` surgery. `T017.lean`'s own 55 receipts are
not reprinted; only the attack receipts are, at the foot.

## What SURVIVED

* Every `theorem` in `T017.lean` re-elaborates. Nothing in it is false.
* **Not vacuous.** §A1 inhabits `ProgramWF` and `CheckedProgram` at a
  non-empty index, on a program with a declared entry, no duplicate ids, no
  dangling target, and two `EC1-CE033`-admissible bodies. `T017.lean` itself
  never inhabits either.
* **The decidability probe comes back GREEN at the modelled clause.** §A9
  gives the `Decidable (AERWF r)` and `Decidable (ProgramWF r)` instances
  `T017.lean` does not write. Its one modelled clause is decidable on the
  nose; nothing semantic is smuggled in. (The eleven UNMODELLED clauses carry
  the whole obligation and are untouched — that is a gap, not a defect.)
* **`EC1-F10` stays green**, generally: §A8 proves `normalizeAER` idempotent
  for every program and every declared triple.
* §4's termination result is real, constructive, and the strongest thing in
  the file.

## What BROKE

1. **§A2 — `.failed` is reachable from `PLine`, and no program can ever
   synthesize it.** The `EC1-T017` report records as a stated omission that
   "the `.failed` refusal arm of `referenceHandler` (`Cas/Lang/Handler.lean`
   :92) is unreachable from `PLine`, so `lineClauses` omits it. That is
   correct for the `PProg` fragment." It is reachable — not through the handler's `.fail` arm but through the
   table walker: `Cas/Lang/Defun.lean`:276 (empty table), :283 (`resolveRefs`
   fails) and :290 (`PIn.resolve` fails) each emit `.refused (.failed _)`.
   Three `rfl`s. And `failed_never_synthesized` proves `.failed` cannot occur
   in `(synthAER r).E` for ANY `r`. So `T017.lean`:816-817 — "The direction
   is over-approximation — the safe direction for a declared type, and not
   the `EC1-F09` too-small-`E` failure" — is FALSE. With the file's own `synthesized_E_is_may_not_must`, the synthesized
   row and the realizable row are INCOMPARABLE: neither containment holds.
   The witness is `T017.lean`'s own `cycProg`. §A2b: the estate already ships
   the decision for two of the three sites (`runP_no_dangling`,
   `Cas/Lang/Defun.lean`:2101) — `Block.body : PProg` simply carries no
   condition, so it was not reused.
2. **§A2 — the cycle scenario's clause is not the clause its block produces.**
   `cycB1.body = [.load (.ans 0)]` refers to answer index 0 at line 0, so
   every run of it refuses with `.failed`, never with `.noObject`
   (`cycB1_never_refuses_noObject`, `rfl`-shaped). The
   `cyc_propagates_across_the_cycle` / `cyc_handler_subtracts` pair is a fact
   about `lineClauses`, not about runs. All three multi-block scenarios also
   have an entry block whose `PProg` body is `[]` — the first `EC1-CE033`
   rejection class.
3. **§A3 — `Realizable` is blind to the block graph.** It reads `bl.body`
   only: never `Term`, never `entry`, never `handles`. `cycProg` and
   `unreachProg` differ ONLY in the entry terminator;
   `realizable_cannot_see_the_terminator` proves their realizable rows
   coincide clause for clause, while `T017.lean` proves their synthesized rows
   differ. So the file's only run-side object cannot distinguish the two
   programs it uses to show the fixpoint is non-degenerate, and §8's may/must
   statement is anchored to a relation with no proved connection to program
   execution.
4. **§A4 — `EC1-F09` fires at the CHECKED carrier on a structurally clean
   program.** `checked_program_omits_a_realizable_clause`: a `CheckedProgram`
   whose declared and synthesized `E` agree exactly, one of whose blocks
   refuses with `.collision` at a concrete address function and word, and
   whose row does not contain `.collision`.
5. **§A5 — `EC1-F05` is red.** `Closed`'s own-contribution arm is
   unconditional, so a direct handler on the block that performs the operation
   subtracts nothing: `f05_own_handler_is_ignored` shows adding or deleting
   the clause changes the row not at all. `ALGEBRA.md`:123 says `E` holds what
   may escape "after direct handlers are applied", and clause 5 `HandlersWF`
   is about "every reachable operation".
6. **§A6/§A7 — `EC1-F03` and `EC1-F01` pass the modelled checker.** Duplicate
   block ids re-open an inheritance path a handler had closed
   (`f03_duplicate_ids_defeat_the_handler`), and deleting a jump target
   silently shrinks `E` (`f01_deleting_the_target_shrinks_E`); both programs
   satisfy `ProgramWF` as `T017.lean` models it. These are `ALGEBRA.md`:299
   clause 1 obligations, and they are exactly what `otherClauses : True`
   assumes away — which is why dropping `ProgramWF` from `EC1-T017a` is a
   strengthening of the PROPOSITION and not of the assurance.
7. **§A10 — the relational reading is EXTENSIONALLY the functional one.**
   `relational_reading_is_the_function_graph` proves `SynthAER r a ↔
   synthAER r = a`. As a definition the split is real; as a predicate the two
   readings are the same, and the equivalence is `synthAER_adequate` plus
   `synthAER_unique`. So all the content sits in `EC1-T017a`, and
   `EC1-T016` at this carrier transports it rather than adding to it.
8. **§A11 — the "computed synthesizer. Total." does not evaluate at scale.**
   Measured, `lake env lean` at default options: a chain of 16 blocks over a
   5-clause alphabet decides in 2.3 s, 26 blocks in 8.5 s, 33 blocks in 13.4 s,
   and 41 blocks fails with `(deterministic) timeout at whnf, maximum number
   of heartbeats (200000)`. Every scenario theorem in `T017.lean` is `by
   decide`, so this is the only evaluation the design exhibits.

## Falsifiers with NO carrier in this row

`EC1-F02` (`Term` carries no `ArgMap` and no answer type, so
`ALGEBRA.md`:279's `EC1-A16 Resume` is not modelled), `EC1-F04`, `EC1-F06`
(`handles` is a flat clause list with no parent link, so clause 5's "named
parent delegation" cannot be represented, let alone cycled), `EC1-F07`,
`EC1-F08`, and `EC1-F81` (`T017.lean` defines no `check`, no `Diagnostic` and
no clause order; there is nothing for a LATER diagnostic to be later than).
`EC1-F09` and `EC1-F10` DO have carriers and are exercised above.
-/

-- BEGIN VERBATIM `T017.lean`:96-1020 -------------------------------------
namespace EC1T017

open Cas Cas.Lang

/-! ## §1 — the carrier

`ALGEBRA.md:284`: "Cycles are ordinary references to earlier blocks." The
block graph is therefore an arbitrary finite directed graph, cycles included,
and that single sentence is what makes this row hard: `E`/`R` synthesis is a
least fixpoint, not a structural recursion.

`Block.body` is the estate's `PProg` (`PROOF-DAG.md:118-121`: "Each proposed
`Block` contains the existing `PProg` as its sequential body"). No second
straight-line carrier is minted, and the error alternatives are the estate's
own `Refusal.Clause` family (`Cas/Lang/RefusalMap.lean:106`), not a new
refusal vocabulary. -/

/-- Block terminators. `branch` is present so the graph is genuinely a graph
and the fixpoint has more than one successor edge to close over. -/
inductive Term where
  | close
  | jump (dst : Nat)
  | branch (thn els : Nat)
  deriving DecidableEq, Repr

/-- The successor block IDs a terminator names. -/
def Term.targets : Term → List Nat
  | .close => []
  | .jump d => [d]
  | .branch a b => [a, b]

/-- `EC1-A11 Block`. `handles` is the block's typed handler clause set (the
alternatives it discharges from its successors); `provides` is its provision
set; `uses` names the service keys its own operations require. -/
structure Block where
  id : Nat
  body : PProg
  handles : List Refusal.Clause
  uses : List Nat
  provides : List Nat
  term : Term

/-- `EC1-D005 AER`. `A` is a `Nat` stand-in for `EC1-D001 ValueTy`. -/
structure AER where
  A : Nat
  E : List Refusal.Clause
  R : List Nat
  deriving DecidableEq, Repr

/-- `EC1-D020 RawProgram`. Dangling jump targets and duplicate block IDs are
deliberately REPRESENTABLE (`ALGEBRA.md:243-246`); nothing below assumes they
are absent. -/
structure RawProgram where
  entry : Nat
  resultTy : Nat
  blocks : List Block
  declared : AER

/-- The declared block IDs, in table order. -/
def blockIds (r : RawProgram) : List Nat := r.blocks.map Block.id

/-- A constructive witness extractor. `List.all_eq_false` in Lean core
carries `Classical.choice` (checked: `#print axioms List.all_eq_false` reports
`[propext, Classical.choice, Quot.sound]`), and §4's whole point is that the
termination bound is constructive — so the lemma is re-proved here by
induction rather than imported. -/
theorem exists_of_all_eq_false {α : Type} {p : α → Bool} :
    ∀ l : List α, l.all p = false → ∃ x, x ∈ l ∧ p x = false
  | [], h => Bool.noConfusion h
  | a :: as, h => by
      rw [List.all_cons, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · exact ⟨a, by simp, h⟩
      · obtain ⟨x, hx, hpx⟩ := exists_of_all_eq_false as h
        exact ⟨x, by simp [hx], hpx⟩

/-! ## §2 — the static fold, generically

`E` and `R` are the same fixpoint at two selectors: what each block
CONTRIBUTES (`own`) and what it SUBTRACTS from its successors (`kill`). The
development is written once, over an arbitrary tag type with decidable
equality, and instantiated twice in §5. -/

section Rows

variable {Tag : Type} [DecidableEq Tag]

/-- A per-block row assignment: which tags stand at which block. -/
abbrev Assign (Tag : Type) := Nat → Tag → Bool

/-- The order on assignments. -/
def Sub (s s' : Assign Tag) : Prop := ∀ b t, s b t = true → s' b t = true

omit [DecidableEq Tag] in
theorem Sub.refl (s : Assign Tag) : Sub s s := fun _ _ h => h

/-- Duplicate removal, hand-rolled so it reduces in the kernel. `List.dedup`
is Mathlib and `library/cas` has no Mathlib (verified: `lake-manifest.json`
lists only `cas`). -/
def nub : List Tag → List Tag
  | [] => []
  | a :: as => if a ∈ nub as then nub as else a :: nub as

theorem mem_nub {x : Tag} : ∀ l : List Tag, x ∈ nub l ↔ x ∈ l
  | [] => by simp [nub]
  | a :: as => by
      by_cases h : a ∈ nub as
      · simp only [nub, if_pos h]
        constructor
        · intro hx; exact List.mem_cons_of_mem _ ((mem_nub as).mp hx)
        · intro hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact h
          · exact (mem_nub as).mpr hx'
      · simp only [nub, if_neg h]
        rw [List.mem_cons, List.mem_cons, mem_nub as]

/-- The program's own finite tag universe, DERIVED from its finite tables
rather than declared. `ALGEBRA.md` gives rows a stable tag/key but never
states per-program finiteness; it follows from the finite block table, and
§4's termination bound is where it is spent. -/
def tagUniverse (r : RawProgram) (own : Block → List Tag) : List Tag :=
  nub (r.blocks.flatMap own)

theorem mem_tagUniverse {r : RawProgram} {own : Block → List Tag} {t : Tag} :
    t ∈ tagUniverse r own ↔ ∃ bl ∈ r.blocks, t ∈ own bl := by
  rw [tagUniverse, mem_nub, List.mem_flatMap]

/-- What a block contributes on its own: the per-OPERATION rows of the
straight-line body. `OpDesc.errorRow` is indexed by the operation, not by the
occurrence and its operands (`ALGEBRA.md:131-141` forces this: a finite
canonical enumeration of a signature's `Sig.Op` is impossible for
`CasE.put (node : Node)` unless the row is keyed per kind). §8 is where that
choice is paid for. -/
def ownB (r : RawProgram) (own : Block → List Tag) (b : Nat) (t : Tag) : Bool :=
  r.blocks.any fun bl => decide (bl.id = b) && decide (t ∈ own bl)

/-- What a block inherits from its successors, minus what it discharges. -/
def inhB (r : RawProgram) (kill : Block → List Tag) (s : Assign Tag)
    (b : Nat) (t : Tag) : Bool :=
  r.blocks.any fun bl =>
    decide (bl.id = b) && !decide (t ∈ kill bl)
      && bl.term.targets.any fun d => s d t

theorem ownB_iff {r : RawProgram} {own : Block → List Tag} {b : Nat} {t : Tag} :
    ownB r own b t = true ↔ ∃ bl ∈ r.blocks, bl.id = b ∧ t ∈ own bl := by
  simp [ownB, List.any_eq_true, Bool.and_eq_true]

theorem inhB_iff {r : RawProgram} {kill : Block → List Tag} {s : Assign Tag}
    {b : Nat} {t : Tag} :
    inhB r kill s b t = true ↔
      ∃ bl ∈ r.blocks, bl.id = b ∧ t ∉ kill bl ∧ ∃ d ∈ bl.term.targets,
        s d t = true := by
  simp [inhB, List.any_eq_true, Bool.and_eq_true, decide_eq_false_iff_not,
    and_assoc]

/-- One propagation step: keep what is already there, add every block's own
contribution, and inherit from successors everything the block does not
discharge. Inflationary by construction. -/
def step (r : RawProgram) (own kill : Block → List Tag) (s : Assign Tag) :
    Assign Tag := fun b t => s b t || ownB r own b t || inhB r kill s b t

theorem step_iff {r : RawProgram} {own kill : Block → List Tag}
    {s : Assign Tag} {b : Nat} {t : Tag} :
    step r own kill s b t = true ↔
      s b t = true ∨ ownB r own b t = true ∨ inhB r kill s b t = true := by
  simp [step, Bool.or_eq_true, or_assoc]

/-- Kleene iteration from the empty assignment. -/
def iter (r : RawProgram) (own kill : Block → List Tag) : Nat → Assign Tag
  | 0 => fun _ _ => false
  | k + 1 => step r own kill (iter r own kill k)

/-- The DECLARATIVE specification, one rule per block. This is `EC1-D023b`:
a `Prop`, defined without reference to `iter`, `step`, or any checker. -/
def Closed (r : RawProgram) (own kill : Block → List Tag) (s : Assign Tag) :
    Prop :=
  ∀ bl ∈ r.blocks, ∀ t : Tag,
    (t ∈ own bl → s bl.id t = true)
      ∧ (t ∉ kill bl → ∀ d ∈ bl.term.targets, s d t = true → s bl.id t = true)

/-- `E` and `R` are the LEAST solution — `ALGEBRA.md:123`'s "exactly the
typed failure alternatives that MAY escape", read as a may-analysis. Coverage
alone admits every over-approximation. -/
def Least (r : RawProgram) (own kill : Block → List Tag) (s : Assign Tag) :
    Prop :=
  Closed r own kill s ∧ ∀ s', Closed r own kill s' → Sub s s'


/-! ## §3 — the fixpoint laws

The route `PROOF-DAG.md:518` names for this family is "structural recursion
plus decidable per-clause reflection", with "using successful examples as
completeness" named as the PROHIBITED shortcut. Nothing below is proved from
an example: §4's bound is a theorem about every program. -/

theorem step_mono {r : RawProgram} {own kill : Block → List Tag}
    {s s' : Assign Tag} (h : Sub s s') :
    Sub (step r own kill s) (step r own kill s') := by
  intro b t ht
  rw [step_iff] at ht ⊢
  rcases ht with ht | ht | ht
  · exact Or.inl (h b t ht)
  · exact Or.inr (Or.inl ht)
  · refine Or.inr (Or.inr ?_)
    rw [inhB_iff] at ht ⊢
    obtain ⟨bl, hbl, hid, hk, d, hd, hsd⟩ := ht
    exact ⟨bl, hbl, hid, hk, d, hd, h d t hsd⟩

theorem le_step {r : RawProgram} {own kill : Block → List Tag}
    (s : Assign Tag) : Sub s (step r own kill s) := by
  intro b t ht
  rw [step_iff]
  exact Or.inl ht

/-- The Kleene chain is increasing. -/
theorem iter_chain (r : RawProgram) (own kill : Block → List Tag) :
    ∀ k, Sub (iter r own kill k) (iter r own kill (k + 1))
  | 0 => by intro b t ht; exact absurd ht (by simp [iter])
  | k + 1 => step_mono (iter_chain r own kill k)

/-- Every iterate lies below every closed assignment. This is the half that
makes the computed value LEAST, and it is proved for all `k` at once — no
appeal to the bound. -/
theorem iter_below {r : RawProgram} {own kill : Block → List Tag}
    {s' : Assign Tag} (hc : Closed r own kill s') :
    ∀ k, Sub (iter r own kill k) s'
  | 0 => by intro b t ht; exact absurd ht (by simp [iter])
  | k + 1 => by
      intro b t ht
      rw [iter, step_iff] at ht
      rcases ht with ht | ht | ht
      · exact iter_below hc k b t ht
      · obtain ⟨bl, hbl, hid, hmem⟩ := ownB_iff.mp ht
        exact hid ▸ (hc bl hbl t).1 hmem
      · obtain ⟨bl, hbl, hid, hk, d, hd, hsd⟩ := inhB_iff.mp ht
        exact hid ▸ (hc bl hbl t).2 hk d hd (iter_below hc k d t hsd)

/-- A post-fixed point of the step function is a closed assignment. -/
theorem closed_of_fix {r : RawProgram} {own kill : Block → List Tag}
    {s : Assign Tag} (hf : Sub (step r own kill s) s) :
    Closed r own kill s := by
  intro bl hbl t
  constructor
  · intro hmem
    exact hf bl.id t (step_iff.mpr (Or.inr (Or.inl (ownB_iff.mpr ⟨bl, hbl, rfl, hmem⟩))))
  · intro hk d hd hsd
    exact hf bl.id t
      (step_iff.mpr (Or.inr (Or.inr (inhB_iff.mpr ⟨bl, hbl, rfl, hk, d, hd, hsd⟩))))

/-- Support: an iterate is `true` only at a declared block and a tag the
program's own tables mention. This is what makes the counting measure in §4
bounded, and it is also what lets bounded stability imply full stability. -/
theorem iter_support {r : RawProgram} {own kill : Block → List Tag} :
    ∀ k b t, iter r own kill k b t = true →
      b ∈ blockIds r ∧ t ∈ tagUniverse r own
  | 0, _, _, ht => absurd ht (by simp [iter])
  | k + 1, b, t, ht => by
      rw [iter, step_iff] at ht
      rcases ht with ht | ht | ht
      · exact iter_support k b t ht
      · obtain ⟨bl, hbl, hid, hmem⟩ := ownB_iff.mp ht
        exact ⟨hid ▸ List.mem_map_of_mem hbl, mem_tagUniverse.mpr ⟨bl, hbl, hmem⟩⟩
      · obtain ⟨bl, hbl, hid, _, d, _, hsd⟩ := inhB_iff.mp ht
        exact ⟨hid ▸ List.mem_map_of_mem hbl, (iter_support k d t hsd).2⟩

/-! ## §4 — termination on a CYCLIC block graph

`ALGEBRA.md:284` makes the block graph cyclic, so the synthesis is a least
fixpoint and not a fold. The scout recorded a termination BOUND as OWED; it
is discharged here. The measure is the number of `true` entries over the
program's own finite block-id list and tag universe, the step is inflationary
and monotone, so the chain either stabilises or strictly gains an entry — and
it cannot gain more than `|blocks| * |alphabet|` of them. -/

omit [DecidableEq Tag] in
theorem cond_le_one (x : Bool) : cond x 1 0 ≤ 1 := by cases x <;> simp

def rowCnt (s : Assign Tag) (b : Nat) : List Tag → Nat
  | [] => 0
  | t :: ts => cond (s b t) 1 0 + rowCnt s b ts

def cnt (s : Assign Tag) (ts : List Tag) : List Nat → Nat
  | [] => 0
  | b :: bs => rowCnt s b ts + cnt s ts bs

omit [DecidableEq Tag] in
theorem rowCnt_le (s : Assign Tag) (b : Nat) :
    ∀ ts : List Tag, rowCnt s b ts ≤ ts.length
  | [] => Nat.le_refl 0
  | t :: ts => by
      have h1 := rowCnt_le s b ts
      have h2 := cond_le_one (s b t)
      simp only [rowCnt, List.length_cons]
      omega

omit [DecidableEq Tag] in
theorem cnt_le (s : Assign Tag) (ts : List Tag) :
    ∀ bs : List Nat, cnt s ts bs ≤ bs.length * ts.length
  | [] => by simp [cnt]
  | b :: bs => by
      have h1 := rowCnt_le s b ts
      have h2 := cnt_le s ts bs
      simp only [cnt, List.length_cons, Nat.succ_mul]
      omega

omit [DecidableEq Tag] in
theorem cond_mono {s s' : Assign Tag} (h : Sub s s') (b : Nat) (t : Tag) :
    cond (s b t) 1 0 ≤ cond (s' b t) 1 0 := by
  cases hb : s b t with
  | false => simp
  | true => simp [h b t hb]

omit [DecidableEq Tag] in
theorem rowCnt_mono {s s' : Assign Tag} (h : Sub s s') (b : Nat) :
    ∀ ts : List Tag, rowCnt s b ts ≤ rowCnt s' b ts
  | [] => Nat.le_refl 0
  | t :: ts => by
      have ih := rowCnt_mono h b ts
      have hc := cond_mono h b t
      simp only [rowCnt]
      omega

omit [DecidableEq Tag] in
theorem cnt_mono {s s' : Assign Tag} (h : Sub s s') (ts : List Tag) :
    ∀ bs : List Nat, cnt s ts bs ≤ cnt s' ts bs
  | [] => Nat.le_refl 0
  | b :: bs => by
      have h1 := rowCnt_mono h b ts
      have h2 := cnt_mono h ts bs
      simp only [cnt]
      omega

-- `DecidableEq Tag` is KEPT here on purpose: `by_cases` on `t = t₀` would
-- otherwise reach for `Classical.em`, and a classical receipt in the
-- termination chain would defeat the point of §4.
theorem rowCnt_lt {s s' : Assign Tag} (h : Sub s s') (b : Nat) {t₀ : Tag}
    (h0 : s b t₀ = false) (h1 : s' b t₀ = true) :
    ∀ ts : List Tag, t₀ ∈ ts → rowCnt s b ts < rowCnt s' b ts
  | [], hm => absurd hm (by simp)
  | t :: ts, hm => by
      have hmono := rowCnt_mono h b ts
      have hc := cond_mono h b t
      by_cases htt : t = t₀
      · subst htt
        simp only [rowCnt, h0, h1, Bool.cond_false, Bool.cond_true]
        omega
      · have hm' : t₀ ∈ ts := by
          rcases List.mem_cons.mp hm with h' | h'
          · exact absurd h'.symm htt
          · exact h'
        have ih := rowCnt_lt h b h0 h1 ts hm'
        simp only [rowCnt]
        omega

theorem cnt_lt {s s' : Assign Tag} (h : Sub s s') (ts : List Tag)
    {b₀ : Nat} {t₀ : Tag} (ht : t₀ ∈ ts)
    (h0 : s b₀ t₀ = false) (h1 : s' b₀ t₀ = true) :
    ∀ bs : List Nat, b₀ ∈ bs → cnt s ts bs < cnt s' ts bs
  | [], hm => absurd hm (by simp)
  | b :: bs, hm => by
      have hmono := cnt_mono h ts bs
      have hrow := rowCnt_mono h b ts
      by_cases hbb : b = b₀
      · subst hbb
        have := rowCnt_lt h b h0 h1 ts ht
        simp only [cnt]; omega
      · have hm' : b₀ ∈ bs := by
          rcases List.mem_cons.mp hm with h' | h'
          · exact absurd h'.symm hbb
          · exact h'
        have ih := cnt_lt h ts ht h0 h1 bs hm'
        simp only [cnt]; omega

/-- The iteration count that suffices. -/
def bound (r : RawProgram) (own : Block → List Tag) : Nat :=
  (blockIds r).length * (tagUniverse r own).length

/-- Bounded stability — decidable, because both quantifiers range over the
program's own finite lists. -/
def stabB (r : RawProgram) (own kill : Block → List Tag) (k : Nat) : Bool :=
  (blockIds r).all fun b => (tagUniverse r own).all fun t =>
    iter r own kill (k + 1) b t == iter r own kill k b t

/-- Bounded stability IS stability, by `iter_support`: off the support both
iterates are `false`. -/
theorem stab_of_stabB {r : RawProgram} {own kill : Block → List Tag} {k : Nat}
    (h : stabB r own kill k = true) :
    iter r own kill (k + 1) = iter r own kill k := by
  funext b t
  by_cases hb : b ∈ blockIds r ∧ t ∈ tagUniverse r own
  · have := (List.all_eq_true.mp h) b hb.1
    have := (List.all_eq_true.mp this) t hb.2
    simpa using this
  · have h1 : iter r own kill (k + 1) b t = false := by
      cases hk : iter r own kill (k + 1) b t with
      | false => rfl
      | true => exact absurd (iter_support (k + 1) b t hk) hb
    have h2 : iter r own kill k b t = false := by
      cases hk : iter r own kill k b t with
      | false => rfl
      | true => exact absurd (iter_support k b t hk) hb
    rw [h1, h2]

/-- Once stable, stable forever. -/
theorem stab_forever {r : RawProgram} {own kill : Block → List Tag} {j : Nat}
    (hs : iter r own kill (j + 1) = iter r own kill j) :
    ∀ n, iter r own kill (j + n) = iter r own kill j
  | 0 => rfl
  | n + 1 => by
      have ih := stab_forever hs n
      show step r own kill (iter r own kill (j + n)) = _
      rw [ih]
      exact hs

/-- The chain either has already stabilised or has gained `k` entries. -/
theorem stab_or_grow (r : RawProgram) (own kill : Block → List Tag) :
    ∀ k, (∃ j, j ≤ k ∧ iter r own kill (j + 1) = iter r own kill j)
      ∨ k ≤ cnt (iter r own kill k) (tagUniverse r own) (blockIds r)
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
      rcases stab_or_grow r own kill k with ⟨j, hjk, hj⟩ | hgrow
      · exact Or.inl ⟨j, Nat.le_succ_of_le hjk, hj⟩
      · cases hst : stabB r own kill k with
        | true => exact Or.inl ⟨k, Nat.le_succ k, stab_of_stabB hst⟩
        | false =>
            refine Or.inr ?_
            have hst' : ((blockIds r).all fun b =>
                (tagUniverse r own).all fun t =>
                  iter r own kill (k + 1) b t == iter r own kill k b t)
                = false := hst
            obtain ⟨b, hb, hbf⟩ := exists_of_all_eq_false _ hst'
            obtain ⟨t, ht, htf⟩ := exists_of_all_eq_false _ hbf
            have hne : iter r own kill (k + 1) b t ≠ iter r own kill k b t := by
              intro he; rw [he] at htf; simp at htf
            have h0 : iter r own kill k b t = false := by
              cases hk : iter r own kill k b t with
              | false => rfl
              | true =>
                  exact absurd ((iter_chain r own kill k b t hk).trans hk.symm) hne
            have h1 : iter r own kill (k + 1) b t = true := by
              cases hk : iter r own kill (k + 1) b t with
              | false => exact absurd (hk.trans h0.symm) hne
              | true => rfl
            have := cnt_lt (iter_chain r own kill k) (tagUniverse r own) ht h0 h1
              (blockIds r) hb
            omega

/-- **The termination theorem.** `|blocks| * |alphabet|` iterations reach a
fixed point, on an arbitrary — cyclic — block graph. -/
theorem stabilises (r : RawProgram) (own kill : Block → List Tag) :
    ∃ j, j ≤ bound r own + 1
      ∧ iter r own kill (j + 1) = iter r own kill j := by
  rcases stab_or_grow r own kill (bound r own + 1) with h | h
  · exact h
  · exact absurd h (by
      have := cnt_le (iter r own kill (bound r own + 1)) (tagUniverse r own)
        (blockIds r)
      simp only [bound] at *
      omega)

/-- The computed solution: iterate to the bound. -/
def sol (r : RawProgram) (own kill : Block → List Tag) : Assign Tag :=
  iter r own kill (bound r own + 1)

theorem sol_fix (r : RawProgram) (own kill : Block → List Tag) :
    step r own kill (sol r own kill) = sol r own kill := by
  obtain ⟨j, hj, hstab⟩ := stabilises r own kill
  have e1 : iter r own kill (bound r own + 1) = iter r own kill j := by
    have := stab_forever hstab (bound r own + 1 - j)
    rwa [Nat.add_sub_cancel' hj] at this
  have e2 : iter r own kill (bound r own + 1 + 1) = iter r own kill j := by
    have := stab_forever hstab (bound r own + 1 + 1 - j)
    rwa [Nat.add_sub_cancel' (Nat.le_succ_of_le hj)] at this
  show iter r own kill (bound r own + 1 + 1) = iter r own kill (bound r own + 1)
  rw [e1, e2]

theorem sol_closed (r : RawProgram) (own kill : Block → List Tag) :
    Closed r own kill (sol r own kill) :=
  closed_of_fix (by rw [sol_fix]; exact Sub.refl _)

theorem sol_least (r : RawProgram) (own kill : Block → List Tag) :
    Least r own kill (sol r own kill) :=
  ⟨sol_closed r own kill, fun _ hc => iter_below hc _⟩

/-! ## §5 — the two synthesizers, and the specification they answer to

The computed row is spelled by FILTERING the program's own canonical tag
alphabet. That is not decoration: `EC1-CE030` / `R16` part 2 says a keyed row
is not determined by its members, and the scout's `coverage_not_unique`
witnesses say the same at the AER carrier. Canonical spelling against a
`nub`-produced alphabet is what makes `SynthRow` single-valued (§6). -/

/-- `EC1-D023a` at the row level — the COMPUTED synthesizer. Total. -/
def synthRow (r : RawProgram) (own kill : Block → List Tag) : List Tag :=
  (tagUniverse r own).filter fun t => sol r own kill r.entry t

/-- `EC1-D023b` at the row level — the DECLARATIVE specification. Note what
it does not mention: `iter`, `step`, `bound`, `sol`, or any checker. It is
not the graph of `synthRow`. -/
def SynthRow (r : RawProgram) (own kill : Block → List Tag)
    (row : List Tag) : Prop :=
  ∃ s, Least r own kill s
    ∧ row = (tagUniverse r own).filter fun t => s r.entry t

/-- The computed row satisfies the declarative specification. -/
theorem synthRow_adequate (r : RawProgram) (own kill : Block → List Tag) :
    SynthRow r own kill (synthRow r own kill) :=
  ⟨sol r own kill, sol_least r own kill, rfl⟩

omit [DecidableEq Tag] in
/-- Two least solutions agree pointwise. -/
theorem least_unique {r : RawProgram} {own kill : Block → List Tag}
    {s s' : Assign Tag} (h : Least r own kill s) (h' : Least r own kill s')
    (b : Nat) (t : Tag) : s b t = s' b t := by
  cases hb : s b t with
  | true => exact (h.2 s' h'.1 b t hb).symm
  | false =>
      cases hb' : s' b t with
      | true => exact absurd (h'.2 s h.1 b t hb') (by simp [hb])
      | false => rfl

/-- The declarative specification is SINGLE-VALUED. This is the substantive
form of `EC1-T016` at this carrier: not `exists!` over a function graph, but
antisymmetry of leastness composed with canonical spelling. -/
theorem synthRow_unique {r : RawProgram} {own kill : Block → List Tag}
    {row row' : List Tag} (h : SynthRow r own kill row)
    (h' : SynthRow r own kill row') : row = row' := by
  obtain ⟨s, hs, rfl⟩ := h
  obtain ⟨s', hs', rfl⟩ := h'
  exact List.filter_congr fun t _ => by rw [least_unique hs hs' r.entry t]

/-- Existence plus uniqueness, in one place, for the row level. -/
theorem synthRow_exists_unique (r : RawProgram) (own kill : Block → List Tag) :
    ∃ row, SynthRow r own kill row ∧ ∀ row', SynthRow r own kill row' → row' = row :=
  ⟨synthRow r own kill, synthRow_adequate r own kill,
    fun _ h => synthRow_unique h (synthRow_adequate r own kill)⟩

end Rows

/-! ## §6 — the two rows of the AER

`E` is instantiated at the estate's own `Refusal.Clause` family and the
per-OPERATION row of the block's `PProg` body. `R` is instantiated at
declared service keys. Nothing is minted: the refusal vocabulary is
`Cas/Lang/RefusalMap.lean:106`'s closed six-arm family and the straight-line
body is `PProg`. -/

/-- The per-OPERATION MAY row, one entry per `PLine` constructor. The `put`
arm is the estate's own admission row (`Refusal.admissionClauses`,
`Cas/Lang/RefusalMap.lean:163`) plus the two non-admission ways
`referenceHandler`'s put clause refuses (`Cas/Lang/Handler.lean:78-88`); the
`load` arm is that clause's only refusal. It is keyed by the operation KIND,
never by the occurrence with its operands — `ALGEBRA.md:131-141` forces that
by requiring a finite canonical enumeration of the signature's `Sig.Op`,
which is impossible for `CasE.put (node : Node)` otherwise. §8 is the price. -/
def lineClauses : PLine → List Refusal.Clause
  | .put _ _ _ _ => Refusal.admissionClauses ++ [.collision, .notWellFormed]
  | .load _ => [.noObject]

/-- A block's own error contribution: the union over its operations. -/
def opsErr (bl : Block) : List Refusal.Clause := bl.body.flatMap lineClauses

/-- `EC1-D023a` — the checker's COMPUTED synthesizer. Total, and bounded by
§4's theorem on an arbitrary cyclic graph. -/
def synthAER (r : RawProgram) : AER :=
  { A := r.resultTy
    E := synthRow r opsErr Block.handles
    R := synthRow r Block.uses Block.provides }

/-- `EC1-D023b` — the DECLARATIVE specification. This is the object the DAG
row's conclusion is about and which `PROOF-DAG.md` §2 never declares. -/
def SynthAER (r : RawProgram) (a : AER) : Prop :=
  a.A = r.resultTy
    ∧ SynthRow r opsErr Block.handles a.E
    ∧ SynthRow r Block.uses Block.provides a.R

/-- **`EC1-T017a`** — THE CONTENT. The computed synthesizer satisfies the
declarative specification: the least fixpoint over the cyclic block graph
exists and bounded iteration computes it.

Note the premise that is NOT here. The DAG-adjacent statement carries
`ProgramWF r`; this one carries nothing. That is a STRENGTHENING, and §9
separates it from vacuity: the specification is not satisfied by every row. -/
theorem synthAER_adequate (r : RawProgram) : SynthAER r (synthAER r) :=
  ⟨rfl, synthRow_adequate r opsErr Block.handles,
    synthRow_adequate r Block.uses Block.provides⟩

/-- `EC1-T016` at this carrier, in its substantive form: the specification is
single-valued. Its proof is antisymmetry of leastness plus canonical
spelling — not `rfl`. -/
theorem synthAER_unique {r : RawProgram} {a b : AER}
    (ha : SynthAER r a) (hb : SynthAER r b) : a = b := by
  have hA : a.A = b.A := by rw [ha.1, hb.1]
  have hE : a.E = b.E := synthRow_unique ha.2.1 hb.2.1
  have hR : a.R = b.R := synthRow_unique ha.2.2 hb.2.2
  cases a; cases b; simp_all

/-- Existence and uniqueness together, at the AER carrier. -/
theorem synthAER_exists_unique (r : RawProgram) :
    ∃ a, SynthAER r a ∧ ∀ b, SynthAER r b → b = a :=
  ⟨synthAER r, synthAER_adequate r, fun _ h => synthAER_unique h (synthAER_adequate r)⟩

/-! ### Scenarios — a genuinely cyclic graph, and handler subtraction

`lean-algebraic-systems`'s gate asks for positive scenarios and deliberately
invalid ones. These are scenarios, NOT the proof: §4 and §6 are proved for
every program, and `PROOF-DAG.md` §16's prohibited shortcut for this family —
"using successful examples as completeness" — is not taken anywhere in this
file. Their value is that they show the fixpoint is not degenerate. -/

/-- Entry block, empty body, jumps to block 1. -/
def cycB0 : Block :=
  { id := 0, body := [], handles := [], uses := [], provides := [],
    term := .jump 1 }

/-- Block 1 loads, contributing `.noObject`, and jumps BACK to block 0. This
is `ALGEBRA.md:284`'s "ordinary reference to an earlier block" — the cycle
that makes the synthesis a fixpoint rather than a fold. -/
def cycB1 : Block :=
  { id := 1, body := [.load (.ans 0)], handles := [], uses := [],
    provides := [], term := .jump 0 }

def cycProg : RawProgram :=
  { entry := 0, resultTy := 0, blocks := [cycB0, cycB1],
    declared := { A := 0, E := [], R := [] } }

/-- The same cycle with the entry block DISCHARGING `.noObject`. -/
def cycB0H : Block := { cycB0 with handles := [.noObject] }

def cycHandled : RawProgram := { cycProg with blocks := [cycB0H, cycB1] }

/-- Positive: the synthesizer terminates on the cycle and propagates block
1's own row back to the entry across it. -/
theorem cyc_propagates_across_the_cycle :
    Refusal.Clause.noObject ∈ (synthAER cycProg).E := by decide

/-- Negative: with the handler in place the clause is GONE. So the computed
row is genuinely the LEAST solution, not a coverage over-approximation —
subtraction bites, and the two scenarios differ only in `handles`. -/
theorem cyc_handler_subtracts :
    Refusal.Clause.noObject ∉ (synthAER cycHandled).E := by decide

/-! ## §7 — the checked carrier, and the DAG row itself -/

/-- Row normalization at the AER carrier: spell the declared triple against
the program's own canonical alphabet. `EC1-CE030` / `R16` part 2 is why this
exists — a keyed row is not determined by its members. -/
def normalizeAER (r : RawProgram) (a : AER) : AER :=
  { A := a.A
    E := (tagUniverse r opsErr).filter fun t => decide (t ∈ a.E)
    R := (tagUniverse r Block.uses).filter fun t => decide (t ∈ a.R) }

/-- `ALGEBRA.md:316` clause 11: "synthesized `A/E/R` normalizes to the
declared triple". -/
def AERWF (r : RawProgram) : Prop := normalizeAER r r.declared = synthAER r

/-- `EC1-D021 ProgramWF`, modelled at ONE clause plus an opaque remainder
standing for `ALGEBRA.md:297-318`'s other eleven. Nothing below reads the
remainder, and §7's findings are about how little even `aerWF` is used. -/
structure ProgramWF (r : RawProgram) : Prop where
  aerWF : AERWF r
  otherClauses : True

/-- `EC1-D023 CheckedProgram`, indexed by the SYNTHESIZED triple — the shape
`check r = .ok ⟨synthAER r, _⟩` forces. -/
structure CheckedProgram (aer : AER) where
  raw : RawProgram
  wf : ProgramWF raw
  idx : synthAER raw = aer

/-- `EC1-D025 erase`. -/
def erase {aer : AER} (p : CheckedProgram aer) : RawProgram := p.raw

/-- **`EC1-T017b`** — the DAG row `checked_aer_exact`, renamed to
`checked_aer_agrees`. `exact` is refuted in §8 and the name must carry the
hedge `EC1-K11` already concedes in prose. -/
theorem checked_aer_agrees {aer : AER} (p : CheckedProgram aer) :
    SynthAER (erase p) aer := by
  obtain ⟨raw, _, idx⟩ := p
  subst idx
  exact synthAER_adequate raw

/-- The same carrier with the `ProgramWF` evidence DELETED. The row still
holds. So `EC1-T017` uses neither `EC1-T010` (`check` does not occur in it),
nor `EC1-T016` (uniqueness does not occur in it), nor the twelve clauses: it
uses `EC1-T017a` and one index field. -/
structure CheckedIndexOnly (aer : AER) where
  raw : RawProgram
  idx : synthAER raw = aer

theorem checked_aer_agrees_needs_no_wf {aer : AER} (p : CheckedIndexOnly aer) :
    SynthAER p.raw aer := by
  obtain ⟨raw, idx⟩ := p
  subst idx
  exact synthAER_adequate raw

/-- The OTHER carrier design: index by the DECLARED triple. Then clause 11 is
the one thing the twelve clauses contribute, and the row costs exactly one
more rewrite. Recording both is the point — which design the packet picks
decides whether `ProgramWF` occurs in `EC1-T017` at all. -/
structure CheckedDeclared (aer : AER) where
  raw : RawProgram
  wf : ProgramWF raw
  idx : normalizeAER raw raw.declared = aer

theorem checked_declared_aer_agrees {aer : AER} (p : CheckedDeclared aer) :
    SynthAER p.raw aer := by
  obtain ⟨raw, wf, idx⟩ := p
  have h : synthAER raw = aer := wf.aerWF.symm.trans idx
  subst h
  exact synthAER_adequate raw

/-! ## §8 — `exact` is false: the synthesized `E` is a MAY row

`EC1-CE008` (VERIFIED-KERNEL) shows the estate's static envelope cannot bound
the CAS error row from above, using the table `[.put 0 0 [] []]`. This
section uses the SAME table from the other side: the row synthesized by
`synthAER` above contains `.dangling`, and no run of that table at any
address function and any starting word can refuse with that clause. The
direction is over-approximation — the safe direction for a declared type, and
not the `EC1-F09` too-small-`E` failure — but a row named `checked_aer_exact`
will be read as exactness, and `PROOF-DAG.md` §16 lists "conflating may and
must" as a PROHIBITED shortcut for this family. -/

/-- One reference-free put. Admissible: the table is nonempty and names no
answer index, so it clears both `EC1-CE033` rejection classes. -/
def freeput : PProg := [.put 0 0 [] []]

def freeBlock : Block :=
  { id := 0, body := freeput, handles := [], uses := [], provides := [],
    term := .close }

def freeProg : RawProgram :=
  { entry := 0, resultTy := 0, blocks := [freeBlock],
    declared := { A := 0, E := [], R := [] } }

/-- The whole synthesized row, spelled canonically against the program's own
alphabet. Recorded so §8's finding is read against a concrete row. -/
theorem freeProg_row :
    (synthAER freeProg).E
      = [.dangling, .wrongKind, .collision, .notWellFormed] := by decide

/-- `.dangling` IS synthesized, because the `put` OPERATION's admission row
declares it. Proved through the closure law, not by kernel evaluation. -/
theorem dangling_synthesized :
    Refusal.Clause.dangling ∈ (synthAER freeProg).E := by
  have hmem : Refusal.Clause.dangling ∈ opsErr freeBlock := by decide
  have hbl : freeBlock ∈ freeProg.blocks := by simp [freeProg]
  refine List.mem_filter.mpr ⟨mem_tagUniverse.mpr ⟨freeBlock, hbl, hmem⟩, ?_⟩
  exact (sol_closed freeProg opsErr Block.handles freeBlock hbl
    Refusal.Clause.dangling).1 hmem

/-- The node this table admits carries no references, so `checkRefs` on it is
`.ok` and `Cas.put` cannot return an admission error (`put_error_iff`,
`Cas/Core/Admission.lean:188`). -/
theorem freeput_node_never_fails_admission
    (H : Bytes → Addr32) (w : Word) (h : Node.WF ⟨0, 0, [], []⟩) :
    ∀ e, Cas.put H (Word.toStore w) ⟨⟨0, 0, [], []⟩, h⟩ ≠ .error e := by
  intro e he
  have := put_error_iff.mp he
  simp [Cas.checkRefs] at this

theorem freeput_refusal_is_the_put_refusal
    (H : Bytes → Addr32) (w : Word) (r : Refusal)
    (h : (runP H freeput w).1 = .refused r) :
    putWord H ⟨0, 0, [], []⟩ w = .error r := by
  cases hp : putWord H ⟨0, 0, [], []⟩ w with
  | ok aw =>
    obtain ⟨a, w'⟩ := aw
    simp [runP, freeput, runPFrom, resolveRefs, hp] at h
  | error r' =>
    simp [runP, freeput, runPFrom, resolveRefs, hp] at h
    exact h ▸ rfl

theorem putWord_freeput_never_dangles
    (H : Bytes → Addr32) (w : Word) (r : Refusal)
    (h : putWord H ⟨0, 0, [], []⟩ w = .error r) :
    r.clause ≠ Refusal.Clause.dangling := by
  have hn : Node.WF (⟨0, 0, [], []⟩ : Node) := by
    constructor <;> simp
  simp only [putWord, referenceHandler, dif_pos hn] at h
  cases hp : Cas.put H (Word.toStore w) ⟨⟨0, 0, [], []⟩, hn⟩ with
  | error e => exact absurd hp (freeput_node_never_fails_admission H w hn e)
  | ok o =>
    cases o with
    | fresh a s => simp [hp] at h
    | duplicate a => simp [hp] at h
    | conflict a m =>
      simp only [hp] at h
      injection h with h
      subst h
      simp [Refusal.clause]

theorem freeput_never_refuses_dangling
    (H : Bytes → Addr32) (w : Word) (r : Refusal)
    (h : (runP H freeput w).1 = .refused r) :
    r.clause ≠ Refusal.Clause.dangling :=
  putWord_freeput_never_dangles H w r (freeput_refusal_is_the_put_refusal H w r h)

/-- The run-side row: a clause SOME run of SOME block of the program
realizes. `EC1-CE042` fixes public meaning as relational, so the must-side of
any exactness claim has to quantify over runs like this. -/
def Realizable (r : RawProgram) (c : Refusal.Clause) : Prop :=
  ∃ (bl : Block) (H : Bytes → Addr32) (w : Word) (ρ : Refusal),
    bl ∈ r.blocks ∧ (runP H bl.body w).1 = .refused ρ ∧ ρ.clause = c

/-- **`EC1-T017c`** — the scope limit. The synthesized `E` is a MAY row and
strictly over-approximates the realizable one, on an ADMISSIBLE program. So
no reading of `checked_aer_exact` whose `exact` means "exact against runs"
is true. -/
theorem synthesized_E_is_may_not_must :
    ¬ ∀ (r : RawProgram) (c : Refusal.Clause),
        c ∈ (synthAER r).E → Realizable r c := by
  intro h
  obtain ⟨bl, H, w, ρ, hbl, hrun, hcl⟩ :=
    h freeProg Refusal.Clause.dangling dangling_synthesized
  have hb : bl = freeBlock := by simpa [freeProg] using hbl
  subst hb
  exact freeput_never_refuses_dangling H w ρ hrun hcl

/-- The same fact as a strict-containment statement. -/
theorem synthE_strictly_over_approximates :
    ∃ (r : RawProgram) (c : Refusal.Clause),
      c ∈ (synthAER r).E ∧ ¬ Realizable r c := by
  refine ⟨freeProg, Refusal.Clause.dangling, dangling_synthesized, ?_⟩
  rintro ⟨bl, H, w, ρ, hbl, hrun, hcl⟩
  have hb : bl = freeBlock := by simpa [freeProg] using hbl
  subst hb
  exact freeput_never_refuses_dangling H w ρ hrun hcl

/-! ## §9 — vacuity, and what is NOT vacuity

Under the FUNCTIONAL reading — `SynthAER` defined as the graph of `synthAER`
— `EC1-T017` is a field projection and `EC1-T016` is premise-free with a
`rfl`-shaped proof. That is the class the packet already deleted at
`EC1-T003`, `EC1-T035`, `EC1-T115`. The split in §6 is what buys content
back, and the last two theorems here are the receipts that it did. -/

def SynthAERFun (r : RawProgram) (a : AER) : Prop := synthAER r = a

/-- `EC1-T017` under the functional reading: one field. -/
theorem functional_reading_makes_T017_a_projection {aer : AER}
    (p : CheckedProgram aer) : SynthAERFun (erase p) aer := p.idx

/-- `EC1-T016` under the functional reading: no premise, proof `⟨_, rfl, _⟩`. -/
theorem functional_reading_makes_T016_premise_free (r : RawProgram) :
    ∃ a, SynthAERFun r a ∧ ∀ b, SynthAERFun r b → b = a :=
  ⟨synthAER r, rfl, fun _ h => h.symm⟩

/-- The relational specification REFUSES rows. `synthAER_unique` is
premise-free too — but premise-free is not vacuous, and this is the
difference: under the functional reading every `a` is `SynthAERFun r a` for
exactly one `a` BY CONSTRUCTION, whereas here the specification has to be
earned against the block graph. -/
theorem SynthAER_refuses_the_empty_row :
    ¬ SynthAER freeProg { A := 0, E := [], R := [] } := by
  intro h
  have he := synthAER_unique h (synthAER_adequate freeProg)
  have hd := dangling_synthesized
  rw [← he] at hd
  simp at hd

/-- And it refuses an over-approximating row: the whole alphabet is closed
but not LEAST, so coverage alone does not satisfy the specification. -/
theorem SynthAER_refuses_an_over_approximation :
    ¬ SynthAER freeProg
        { A := 0, E := [.dangling, .wrongKind, .collision, .notWellFormed],
          R := [0] } := by
  intro h
  have he := synthAER_unique h (synthAER_adequate freeProg)
  have : (0 : Nat) ∈ (synthAER freeProg).R := by rw [← he]; simp
  have hR : (synthAER freeProg).R = [] := by
    show synthRow freeProg Block.uses Block.provides = []
    simp [synthRow, tagUniverse, freeProg, freeBlock, nub]
  rw [hR] at this
  simp at this

/-! ## §10 — the divergence, made checkable

Six of these eight rows target one module and sibling agents are building
`RawProgram` / `ProgramWF` / `check` right now. Their `synthAER` (read, not
guessed: `T010.lean:700`, `T011.lean:218`, `T012.lean:511`, `T013.lean:375`;
`T014.lean:403` is an explicit placeholder) is in every case a WHOLE-TABLE
FOLD over `r.blocks` — no entry rooting, no successor closure, no handler
subtraction — and `SynthAER` is read as its graph.

That is not a stylistic difference. The whole-table fold is exactly the tag
ALPHABET this file derives, and the fixpoint row is a subset of it that is
generally PROPER. The two theorems below exhibit both ways the subset is
strict. Until the packet rules which object `E` is, `EC1-T016`, `EC1-T017`,
`EC1-T087` and `EC1-T108` are about different things in different files. -/

/-- The sibling synthesizers' shape, at this carrier. -/
def tableFoldE (r : RawProgram) : List Refusal.Clause :=
  nub (r.blocks.flatMap opsErr)

/-- And it is literally the alphabet: the whole-table fold computes the
universe the fixpoint then filters. -/
theorem the_fold_is_the_alphabet (r : RawProgram) :
    tableFoldE r = tagUniverse r opsErr := rfl

/-- Entry block, empty body, returns. Block 1 raises but is UNREACHABLE. -/
def unreachB0 : Block :=
  { id := 0, body := [], handles := [], uses := [], provides := [],
    term := .close }

def unreachProg : RawProgram :=
  { entry := 0, resultTy := 0, blocks := [unreachB0, cycB1],
    declared := { A := 0, E := [], R := [] } }

/-- Divergence 1 — REACHABILITY. An unreachable block's alternatives are in
the fold and not in the fixpoint row. -/
theorem fold_counts_unreachable_blocks :
    Refusal.Clause.noObject ∈ tableFoldE unreachProg
      ∧ Refusal.Clause.noObject ∉ (synthAER unreachProg).E := by decide

/-- Divergence 2 — HANDLER SUBTRACTION. A discharged alternative is in the
fold and not in the fixpoint row. Note this one is invisible to any
whole-table fold no matter how reachability is settled. -/
theorem fold_ignores_handler_subtraction :
    Refusal.Clause.noObject ∈ tableFoldE cycHandled
      ∧ Refusal.Clause.noObject ∉ (synthAER cycHandled).E := by decide

end EC1T017
-- END VERBATIM `T017.lean`:96-1020 ---------------------------------------

/-! ## §A — the attack -/

namespace AttackT017

open Cas Cas.Lang EC1T017

/-! ### §A0 — shared witnesses -/

def z : Addr32 := ⟨List.replicate 32 0, by simp⟩
def Hz : Bytes → Addr32 := fun _ => z
def n1 : Node := ⟨1, 0, [], []⟩
/-- A word whose only binding sits at `Hz`'s single address and holds a
DIFFERENT node, so `Cas.put` lands in `.conflict`. -/
def wC : Word := [⟨z, n1⟩]

/-- `EC1-CE033`-admissible bodies: nonempty tables naming no answer index. -/
def loadLit : PProg := [.load (.lit z)]
def putFree : PProg := [.put 0 0 [] []]

/-! ### §A1 — non-vacuity of the checked carrier

`ProgramWF` as `T017.lean` models it is INHABITED, so none of the eight rows
is empty for want of a hypothesis. The witness uses two `EC1-CE033`-admissible
bodies, a declared entry, no duplicate ids and no dangling target. -/

def reachBlock : Block :=
  { id := 0, body := loadLit, handles := [], uses := [], provides := [],
    term := .close }

def hiddenBlock : Block :=
  { id := 1, body := putFree, handles := [], uses := [], provides := [],
    term := .close }

def twoProg : RawProgram :=
  { entry := 0, resultTy := 0, blocks := [reachBlock, hiddenBlock],
    declared := { A := 0, E := [], R := [] } }

/-- The same program with its declared triple set to what the synthesizer
computes. Nothing circular: `synthAER` reads `entry`, `resultTy` and `blocks`
only, never `declared`. -/
def wfProg : RawProgram := { twoProg with declared := synthAER twoProg }

theorem wfProg_is_aerWF : AERWF wfProg := by
  show normalizeAER wfProg wfProg.declared = synthAER wfProg
  decide

def wfChecked : CheckedProgram (synthAER wfProg) :=
  { raw := wfProg, wf := ⟨wfProg_is_aerWF, trivial⟩, idx := rfl }

/-- Non-vacuity, stated: the hypothesis of `EC1-T017b` is inhabitable at a
non-degenerate index. -/
theorem programWF_is_inhabited : ∃ r : RawProgram, ProgramWF r ∧ (synthAER r).E ≠ [] :=
  ⟨wfProg, ⟨wfProg_is_aerWF, trivial⟩, by decide⟩

/-! ### §A2 — THE BREAK: `.failed` is reachable from `PLine`, and can never
be synthesized

`T017.lean` records as a stated omission that "the `.failed` refusal arm of
`referenceHandler` is unreachable from `PLine`, so `lineClauses` omits it",
and §8's doc comment claims "the direction is over-approximation — the safe
direction for a declared type, and not the `EC1-F09` too-small-`E` failure".

Both are false. `.failed` reaches `PLine` NOT through `referenceHandler`'s
`.fail` arm but through the table walker itself: `Cas/Lang/Defun.lean`:276
(`runPFrom` on the empty table), :283 (`resolveRefs` returns `none`) and :290
(`PIn.resolve` returns `none`) each emit `.refused (.failed _)`. The first
three theorems below are `rfl`. -/

theorem runP_empty_body_refuses_failed (H : Bytes → Addr32) (w : Word) :
    (runP H [] w).1 = .refused (.failed "defun: empty program") := rfl

theorem runP_dangling_load_index_refuses_failed (H : Bytes → Addr32) (w : Word) :
    (runP H [.load (.ans 0)] w).1
      = .refused (.failed "defun: dangling answer index") := rfl

theorem runP_dangling_put_index_refuses_failed (H : Bytes → Addr32) (w : Word) :
    (runP H [.put 0 0 [] [(0, .ans 0)]] w).1
      = .refused (.failed "defun: dangling answer index") := rfl

/-- `lineClauses` cannot name `.failed`, at any line. -/
theorem failed_not_in_lineClauses (l : PLine) :
    Refusal.Clause.failed ∉ lineClauses l := by
  cases l <;> simp [lineClauses, Refusal.admissionClauses]

/-- Hence NO program's synthesized `E` can ever contain `.failed`. This is a
theorem about every `RawProgram`, not a scenario. -/
theorem failed_never_synthesized (r : RawProgram) :
    Refusal.Clause.failed ∉ (synthAER r).E := by
  intro h
  have h1 : Refusal.Clause.failed ∈ tagUniverse r opsErr :=
    (List.mem_filter.mp h).1
  obtain ⟨bl, _, hbl⟩ := mem_tagUniverse.mp h1
  obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp hbl
  exact failed_not_in_lineClauses l hl

/-- `T017.lean`'s OWN cycle scenario realizes `.failed`: `cycB0.body = []`,
so every run of that block, at every address function and every word,
refuses with `.failed`. -/
theorem cycProg_realizes_failed : Realizable cycProg Refusal.Clause.failed :=
  ⟨cycB0, Hz, [], .failed "defun: empty program", by simp [cycProg], rfl, rfl⟩

/-- **The refutation of `T017.lean` §8's direction claim.** The synthesized
`E` is not an over-approximation of the realizable row either. Together with
the file's own `synthesized_E_is_may_not_must`, the two rows are INCOMPARABLE:
no containment holds in either direction. -/
theorem synth_E_does_not_over_approximate_realizable :
    ¬ ∀ (r : RawProgram) (c : Refusal.Clause), Realizable r c → c ∈ (synthAER r).E :=
  fun h => failed_never_synthesized cycProg (h cycProg _ cycProg_realizes_failed)

theorem synth_E_is_strictly_under_as_well :
    ∃ (r : RawProgram) (c : Refusal.Clause),
      Realizable r c ∧ c ∉ (synthAER r).E :=
  ⟨cycProg, Refusal.Clause.failed, cycProg_realizes_failed,
    failed_never_synthesized cycProg⟩

/-- The same defect at the file's `unreachProg` and `cycHandled`: all three of
its multi-block scenarios have an entry block with an empty `PProg` body. -/
theorem all_cycle_scenarios_realize_failed :
    Realizable cycHandled Refusal.Clause.failed
      ∧ Realizable unreachProg Refusal.Clause.failed :=
  ⟨⟨cycB0H, Hz, [], .failed "defun: empty program", by simp [cycHandled, cycProg], rfl, rfl⟩,
   ⟨unreachB0, Hz, [], .failed "defun: empty program", by simp [unreachProg], rfl, rfl⟩⟩

/-- And `cycB1`, the block whose `.noObject` the file propagates across the
cycle, can NEVER refuse with `.noObject`: its `.ans 0` operand is out of range
at line 0, so every run refuses with `.failed` first. The scenario's
positive claim is a statement about `lineClauses`, not about runs. -/
theorem cycB1_never_refuses_noObject (H : Bytes → Addr32) (w : Word)
    (ρ : Refusal) (h : (runP H cycB1.body w).1 = .refused ρ) :
    ρ.clause ≠ Refusal.Clause.noObject := by
  have : ρ = .failed "defun: dangling answer index" := by
    have hr : (runP H cycB1.body w).1
        = .refused (.failed "defun: dangling answer index") := rfl
    rw [hr] at h
    injection h.symm
  subst this
  simp [Refusal.clause]

/-! ### §A2b — the estate already decides HALF the gap, and `T017.lean` did not
reuse it

`Cas/Lang/Defun.lean`:2101 ships `runP_no_dangling`: a table whose envelope
reports a closed dataflow never refuses with the dangling-index `.failed`, at
any word, decided before anything runs. That is exactly the per-block clause
this carrier needs and does not have — `Block.body : PProg` carries no
condition at all. It covers the :283/:290 sites and NOT the :276 one: the
empty table's envelope is dataflow-closed, so the empty-program `.failed`
needs a separate nonemptiness clause. `EC1-CE033` already names both classes,
and `R15` already rules ingress partial. -/

theorem cycB1_body_is_not_dataflow_closed :
    (PProg.envelope cycB1.body).dataflowClosed = false := by decide

theorem the_admissible_bodies_are_dataflow_closed :
    (PProg.envelope putFree).dataflowClosed = true
      ∧ (PProg.envelope loadLit).dataflowClosed = true := by decide

/-- And the shipped decision does NOT reach the empty table: the second
`EC1-CE033` class needs its own clause. -/
theorem the_empty_table_passes_the_shipped_decision :
    (PProg.envelope ([] : PProg)).dataflowClosed = true
      ∧ (runP Hz ([] : PProg) []).1 = .refused (.failed "defun: empty program") :=
  ⟨by decide, rfl⟩

/-! ### §A3 — `Realizable` is blind to the block graph

`Realizable` reads `bl.body` only. It never mentions `Term`, `entry` or
`handles`, so it cannot see the three things the fixpoint is built out of.
`cycProg` and `unreachProg` differ ONLY in the entry block's terminator; the
file proves their synthesized rows differ, and the rows below prove their
realizable rows do not. So `synthAER.E` is not a function of the realizable
row and the realizable row is not a function of `synthAER.E`: §8's may/must
statement is anchored to a relation with no proved connection to the object
the synthesizer computes. -/

theorem realizable_cannot_see_the_terminator (c : Refusal.Clause) :
    Realizable cycProg c ↔ Realizable unreachProg c := by
  constructor
  · rintro ⟨bl, H, w, ρ, hbl, hrun, hcl⟩
    rcases (by simpa [cycProg] using hbl : bl = cycB0 ∨ bl = cycB1) with rfl | rfl
    · exact ⟨unreachB0, H, w, ρ, by simp [unreachProg], hrun, hcl⟩
    · exact ⟨cycB1, H, w, ρ, by simp [unreachProg], hrun, hcl⟩
  · rintro ⟨bl, H, w, ρ, hbl, hrun, hcl⟩
    rcases (by simpa [unreachProg] using hbl : bl = unreachB0 ∨ bl = cycB1) with rfl | rfl
    · exact ⟨cycB0, H, w, ρ, by simp [cycProg], hrun, hcl⟩
    · exact ⟨cycB1, H, w, ρ, by simp [cycProg], hrun, hcl⟩

theorem synth_E_separates_what_realizable_identifies :
    (∀ c, Realizable cycProg c ↔ Realizable unreachProg c)
      ∧ (synthAER cycProg).E ≠ (synthAER unreachProg).E :=
  ⟨realizable_cannot_see_the_terminator, by decide⟩

/-! ### §A4 — `EC1-F09` at the CHECKED carrier, on a structurally clean program

`twoProg` has a declared entry, no duplicate ids, no dangling target, and two
`EC1-CE033`-admissible bodies. Its second block is unreachable, so the
fixpoint drops that block's clauses — while `Realizable`, the file's only
run-side object, keeps them. -/

theorem twoProg_realizes_collision : Realizable twoProg Refusal.Clause.collision :=
  ⟨hiddenBlock, Hz, wC, .collision z, by simp [twoProg], rfl, rfl⟩

theorem twoProg_row_omits_collision :
    Refusal.Clause.collision ∉ (synthAER twoProg).E := by decide

/-- A program that passes every clause `T017.lean` models, whose declared and
synthesized `E` agree exactly, and one of whose blocks refuses with a clause
that row does not contain. -/
theorem checked_program_omits_a_realizable_clause :
    ∃ (aer : AER) (p : CheckedProgram aer),
      Realizable (erase p) Refusal.Clause.collision
        ∧ Refusal.Clause.collision ∉ aer.E :=
  ⟨synthAER wfProg, wfChecked,
    ⟨hiddenBlock, Hz, wC, .collision z, by simp [erase, wfChecked, wfProg, twoProg],
      rfl, rfl⟩,
    by decide⟩

/-! ### §A5 — `EC1-F05`: a block's own handler clause is ignored

`ALGEBRA.md`:123 says `E` holds the alternatives that may escape "after
direct handlers are applied", and clause 5 `HandlersWF` is about "every
reachable operation". `T017.lean`'s `Closed` applies `kill` only to the
INHERITANCE arm: the own-contribution arm `t ∈ own bl → s bl.id t = true` is
unconditional. So a direct handler on the very block that performs the
operation subtracts nothing, and omitting it changes nothing. -/

def selfH : Block :=
  { id := 0, body := loadLit, handles := [.noObject], uses := [], provides := [],
    term := .close }

def selfB : Block := { selfH with handles := [] }

def selfProgH : RawProgram :=
  { entry := 0, resultTy := 0, blocks := [selfH],
    declared := { A := 0, E := [], R := [] } }

def selfProgB : RawProgram := { selfProgH with blocks := [selfB] }

theorem f05_own_handler_is_ignored :
    (synthAER selfProgH).E = (synthAER selfProgB).E
      ∧ Refusal.Clause.noObject ∈ (synthAER selfProgH).E := by decide

/-! ### §A6 — `EC1-F03`: duplicate block ids merge silently and defeat a handler

`ALGEBRA.md`:299 clause 1 `IdsWF` requires duplicate-free tables. `T017.lean`
models no such clause (`otherClauses : True`), and `ownB`/`inhB` quantify over
BLOCKS while the assignment is keyed by ID — so a second block sharing an id
re-opens an inheritance path the first block's handler had closed. -/

def dupA : Block :=
  { id := 0, body := putFree, handles := [.noObject], uses := [], provides := [],
    term := .jump 1 }

def dupB : Block := { dupA with handles := [] }

def dupTarget : Block :=
  { id := 1, body := loadLit, handles := [], uses := [], provides := [],
    term := .close }

def singleProg : RawProgram :=
  { entry := 0, resultTy := 0, blocks := [dupA, dupTarget],
    declared := { A := 0, E := [], R := [] } }

def dupProg : RawProgram := { singleProg with blocks := [dupA, dupB, dupTarget] }

theorem f03_duplicate_ids_defeat_the_handler :
    Refusal.Clause.noObject ∉ (synthAER singleProg).E
      ∧ Refusal.Clause.noObject ∈ (synthAER dupProg).E := by decide

def dupWF : RawProgram := { dupProg with declared := synthAER dupProg }

theorem f03_the_duplicate_program_still_checks : ProgramWF dupWF :=
  ⟨by show normalizeAER dupWF dupWF.declared = synthAER dupWF; decide, trivial⟩

/-! ### §A7 — `EC1-F01`: deleting a jump target shrinks `E` and still checks

Clause 1's "every reference resolves" is likewise unmodelled. A target that
names no block contributes nothing to the least solution, so deleting a block
is indistinguishable from that block having an empty row. -/

def f01Entry : Block :=
  { id := 0, body := loadLit, handles := [], uses := [], provides := [],
    term := .jump 1 }

def f01Full : RawProgram :=
  { entry := 0, resultTy := 0, blocks := [f01Entry, hiddenBlock],
    declared := { A := 0, E := [], R := [] } }

def f01Cut : RawProgram := { f01Full with blocks := [f01Entry] }

theorem f01_deleting_the_target_shrinks_E :
    Refusal.Clause.collision ∈ (synthAER f01Full).E
      ∧ Refusal.Clause.collision ∉ (synthAER f01Cut).E := by decide

def f01CutWF : RawProgram := { f01Cut with declared := synthAER f01Cut }

theorem f01_the_cut_program_still_checks : ProgramWF f01CutWF :=
  ⟨by show normalizeAER f01CutWF f01CutWF.declared = synthAER f01CutWF; decide,
    trivial⟩

/-! ### §A8 — `EC1-F10` stays GREEN: row normalization is idempotent

Proved generally rather than on a witness, so the falsifier is closed for
every program and every declared triple. -/

theorem f10_normalizeAER_is_idempotent (r : RawProgram) (a : AER) :
    normalizeAER r (normalizeAER r a) = normalizeAER r a := by
  simp only [normalizeAER, AER.mk.injEq, true_and]
  refine ⟨List.filter_congr fun t ht => ?_, List.filter_congr fun t ht => ?_⟩ <;>
    simp [List.mem_filter, ht]

/-! ### §A9 — the decidability probe comes back GREEN, at one clause

The brief's highest-value target is a `ProgramWF` clause that is silently
semantic. `T017.lean` models exactly one, and it IS decidable — here is the
instance the file does not write. Note what this does NOT establish: the
eleven unmodelled clauses of `ALGEBRA.md`:297-318 carry the whole decidability
obligation and none of them is touched. -/

instance instDecidableAERWF (r : RawProgram) : Decidable (AERWF r) := by
  unfold AERWF; infer_instance

instance instDecidableProgramWF (r : RawProgram) : Decidable (ProgramWF r) :=
  match instDecidableAERWF r with
  | isTrue h => isTrue ⟨h, trivial⟩
  | isFalse h => isFalse fun p => h p.aerWF

/-! ### §A10 — the relational reading is EXTENSIONALLY the functional one

`T017.lean` §9 separates "premise-free" from "vacuous" and says its
`SynthAER` "is NOT the graph of `synthAER`". As a DEFINITION that is true.
As a PREDICATE the two are provably the same, and the equivalence is exactly
`EC1-T017a` plus `EC1-T016`. So the content the split buys sits entirely in
`synthAER_adequate`; `synthAER_unique` transports it and adds nothing that
the functional reading does not already have. -/

theorem relational_reading_is_the_function_graph (r : RawProgram) (a : AER) :
    SynthAER r a ↔ SynthAERFun r a :=
  ⟨fun h => synthAER_unique (synthAER_adequate r) h, fun h => h ▸ synthAER_adequate r⟩

/-- And therefore the DAG row, at either reading, is one field of its input. -/
theorem the_row_is_the_index_either_way {aer : AER} (p : CheckedProgram aer) :
    SynthAER (erase p) aer ∧ SynthAERFun (erase p) aer :=
  ⟨checked_aer_agrees p, p.idx⟩

/-! ### §A11 — the computed synthesizer does not evaluate at scale

`T017.lean` calls `synthAER` "the checker's COMPUTED synthesizer. Total."
Totality is proved; usability is not, and `decide` is the only evaluator any
theorem in that file exercises. `sol` is `iter (bound + 1)` with
`bound = |blocks| * |alphabet|`, and a query re-walks the whole chain.

Measured with `lake env lean` at default options on the family below
(`n` put-blocks in a jump chain plus one unreachable load-block, so the
alphabet is 5 and the answer is `false`, which cannot short-circuit):

```text
n+1 blocks   bound   wall
     16        80    2.3 s
     26       130    8.5 s
     33       165   13.4 s
     41       205   error: (deterministic) timeout at `whnf`,
                    maximum number of heartbeats (200000) has been reached
```

The live probe below is kept small so this file stays fast. -/

def probeBlk (i n : Nat) : Block :=
  { id := i, body := putFree, handles := [], uses := [], provides := [],
    term := if i + 1 < n then .jump (i + 1) else .close }

def probeFar : Block :=
  { id := 999, body := loadLit, handles := [], uses := [], provides := [],
    term := .close }

/-- `n` reachable put-blocks in a chain, plus one unreachable load-block. -/
def probeChain (n : Nat) : RawProgram :=
  { entry := 0, resultTy := 0,
    blocks := (List.range n).map (fun i => probeBlk i n) ++ [probeFar],
    declared := { A := 0, E := [], R := [] } }

set_option maxRecDepth 100000 in
theorem probe_chain_8 :
    Refusal.Clause.noObject ∉ (synthAER (probeChain 8)).E := by decide

/-! ### §A12 — checker compatibility across `EC1-S2`, as read

Read from the eight files, not guessed. `T017.lean` §10 records that the
sibling `synthAER`s are whole-table folds. The divergence is wider than that:
the `AER` CARRIER differs too, so six of the eight rows are about different
types.

| File | `AER` | `ProgramWF` |
| --- | --- | --- |
| `T010.lean`:263,748 | `{A : Nat, E R : List Nat}` | 12 clauses |
| `T011.lean`:97,258 | `{E R : List OpId}` — no `A` | 4 clauses |
| `T012.lean`:453,517 | `{A : Nat, E : List ErrTag}` — no `R` | 3 clauses |
| `T013.lean`:334,380 | `List Alt` — a bare row | 4 clauses |
| `T014.lean`:400,322 | `Nat` | 6 clauses, env-indexed |
| `T016.lean`:298 | (row only) | 2 clauses |
| `T017.lean`:139,756 | `{A : Nat, E : List Refusal.Clause, R : List Nat}` | 1 clause + `True` |

Only `AERWF` occurs in every checker that has one (`T014.lean` has none), and
even that clause has three orientations: `synthAER r = r.declared` on the nose
(`T010.lean`:705, `T011.lean`:255, `T012.lean`:514, `T013.lean`:378), canon on
the DECLARED side (`T016.lean`:296 `canon r.declaredE = synthE r`), and
normalization on the declared side against a DERIVED alphabet
(`T017.lean`:751). `T014.lean`:403's `synthAER r := r.blocks.length` is an
explicit placeholder.

`T017.lean` is the only file in the slice whose `E` is the estate's own
`Refusal.Clause` and whose observation model reaches the shipped `runP`. That
is the strongest thing about its carrier, and it is also why §A2's break is
available here and nowhere else: the other seven cannot state a run-side claim
at all. -/

end AttackT017

/-! ## Attack receipts -/

#print axioms AttackT017.runP_empty_body_refuses_failed
#print axioms AttackT017.runP_dangling_load_index_refuses_failed
#print axioms AttackT017.runP_dangling_put_index_refuses_failed
#print axioms AttackT017.failed_not_in_lineClauses
#print axioms AttackT017.failed_never_synthesized
#print axioms AttackT017.cycProg_realizes_failed
#print axioms AttackT017.synth_E_does_not_over_approximate_realizable
#print axioms AttackT017.synth_E_is_strictly_under_as_well
#print axioms AttackT017.all_cycle_scenarios_realize_failed
#print axioms AttackT017.cycB1_never_refuses_noObject
#print axioms AttackT017.cycB1_body_is_not_dataflow_closed
#print axioms AttackT017.the_admissible_bodies_are_dataflow_closed
#print axioms AttackT017.the_empty_table_passes_the_shipped_decision
#print axioms AttackT017.realizable_cannot_see_the_terminator
#print axioms AttackT017.synth_E_separates_what_realizable_identifies
#print axioms AttackT017.wfProg_is_aerWF
#print axioms AttackT017.programWF_is_inhabited
#print axioms AttackT017.twoProg_realizes_collision
#print axioms AttackT017.twoProg_row_omits_collision
#print axioms AttackT017.checked_program_omits_a_realizable_clause
#print axioms AttackT017.f05_own_handler_is_ignored
#print axioms AttackT017.f03_duplicate_ids_defeat_the_handler
#print axioms AttackT017.f03_the_duplicate_program_still_checks
#print axioms AttackT017.f01_deleting_the_target_shrinks_E
#print axioms AttackT017.f01_the_cut_program_still_checks
#print axioms AttackT017.f10_normalizeAER_is_idempotent
#print axioms AttackT017.relational_reading_is_the_function_graph
#print axioms AttackT017.the_row_is_the_index_either_way
#print axioms AttackT017.probe_chain_8
