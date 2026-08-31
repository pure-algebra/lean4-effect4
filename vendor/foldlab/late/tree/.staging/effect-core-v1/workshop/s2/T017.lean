import Cas.Lang.Defun
import Cas.Lang.RefusalMap

/-!
# Effect Core v1 — `EC1-T017`, slice `EC1-S2` (admission boundary)

Row under implementation (`PROOF-DAG.md:219`):

```text
EC1-T017  checked_aer_exact : p : CheckedProgram aer -> SynthAER (erase p) aer
          depends on: T010, T016
```

Intended home, NOT written by this file:
`formal/effect-core-v1/EffectCore/Admission/Check.lean` (re-verified: still
the reserved empty boundary — a doc comment, `namespace EffectCore.Admission`,
`end`, no declarations).

Skill stage: `.claude/skills/lean/workflows/lean-algebraic-systems/SKILL.md`.
This row is an OPERATION question, not a representation question: the object
it is about is a synthesizer — a least fixpoint over a cyclic block graph —
so the stage is `lean-algebraic-systems`, not `lean-model-invariants`. Its
"separate the semantic artifacts" list is followed literally below: §2 is the
static fold (item 4), §3-§5 are its interpreter and preservation laws (items
5 and 7), §7 is the checked-carrier boundary, §8 is the observation law
against the estate's real interpreter (item 6).

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/T017.lean
```

## What this file does

`SynthAER` is used by `EC1-T016` and `EC1-T017` and has NO `PROPOSED TERM`
node anywhere in `PROOF-DAG.md` §2 (grepped: two hits, both inside the
theorem table). So the row's conclusion is about an object the packet never
declares. This file makes the scout's required split and then proves the row
against it:

* `synthAER : RawProgram -> AER` — the checker's COMPUTED synthesizer,
  bounded Kleene iteration over the block graph (§5). Total.
* `SynthAER : RawProgram -> AER -> Prop` — the DECLARATIVE specification:
  `E` and `R` are the LEAST assignment closed under each block's own
  operation rows, under successor blocks, and under handler/provision
  subtraction (§3). It is NOT the graph of `synthAER`.

Everything then follows from ONE theorem with real content, `EC1-T017a`
(§6): the computed synthesizer lands on the declaratively specified least
fixpoint. `EC1-T017b` — the DAG row itself — is that theorem transported
along a structure field (§7), and `EC1-T017c` (§8) is the scope limit that
stops either name from being read as exactness against runs.

A successful elaboration below proves the stated propositions and NOTHING
more. It is not model assurance, not implementation assurance, and it closes
no proof-DAG row.

## Findings

| § | Question | Finding |
|---|---|---|
| 4 | Does the fixpoint terminate on a CYCLIC block graph? | YES, and the bound is proved: `|blocks| * |alphabet| + 1` iterations suffice (`stabilises`, `sol_fix`). This is the obligation the scout recorded as OWED; it is discharged here. |
| 6 | Is `EC1-T017a` conditional on `ProgramWF`? | NO. Proved with no premise at all. Not vacuous either — §9 exhibits rows the spec REFUSES. |
| 7 | Does the DAG row use `T010` or `T016`? | Neither. `check` does not occur in it, and uniqueness does not occur in it. It uses `EC1-T017a` and one index field. The `ProgramWF` evidence is unused too. |
| 8 | Is `exact` true? | NO. `.dangling` is synthesized into `E` for a one-line reference-free `put` that no run at any address function and any word can refuse with. `exact` must become `agrees`. |
| 9 | Is `EC1-T016` vacuous? | Under the FUNCTIONAL reading, yes (proved). At the relational carrier built here it is premise-free but SUBSTANTIVE — its proof is antisymmetry of leastness, not `rfl`. "Premise-free" and "vacuous" are different findings. |
| 10 | Is `SynthAER` alone enough? | NO. Uniqueness holds only because rows are spelled canonically against the program's own tag alphabet. Member-level closure is not unique (`EC1-CE030` at the AER carrier). |
| 10 | Do the eight agents share one `synthAER`? | NO, and the gap is checked. Every sibling's `synthAER` is a whole-table FOLD; the fold is exactly this file's tag alphabet, and the fixpoint row is a PROPER subset of it — strictly, in two independent ways (unreachable blocks, handler subtraction). |

## Checks omitted, stated up front

* `ProgramWF` is modelled with ONE clause, `AERWF` (`ALGEBRA.md:316`,
  clause 11), plus an opaque remainder. The other eleven clauses are NOT
  modelled and nothing here claims they are decidable. Sibling agents
  `T010`-`T015` build five- and six-clause checkers; see `divergenceFromDag`.
* No clause is proved undecidable. That is not expressible in Lean without a
  computability model, and every `Prop` is classically `Decidable`.
* `check` (`EC1-D024`) is NOT defined here. `EC1-T017` does not mention it;
  §7 records that as a finding rather than papering over it with a checker
  this row cannot constrain.
* `EC1-T006 normalizeRaw_idempotent` / `EC1-T007` are `EC1-S1` rows running
  concurrently in `workshop/s1/`, which this file did not read. §7 states the
  one place normalization enters as an explicit hypothesis, not a result.
* The `A` component of `AER` is a `Nat` stand-in for `EC1-D001 ValueTy`
  (`PROOF-DAG.md` §17 condition 1 is OPEN). Only `E` and `R` carry the
  fixpoint content.
* `R`'s service keys are a declared `List Nat` per block. The estate has no
  service carrier at all, so nothing anchors them; the `E` row IS anchored,
  at `Refusal.Clause` and the shipped `runP`.
* Falsifiers `F01-F10` / `F81` were not run: they have no carriers.
* Nothing in `library/`, `formal/effect-core-v1/`, or any packet `.md` was
  modified, and no writing git command was run.
-/

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

/-! ## Kernel receipts

Every theorem in the file. `propext` and `Quot.sound` are inherited from
`simp`, `omega` and `funext`; `Classical.choice` appears NOWHERE, which is
the load-bearing receipt for §4: the termination bound is constructive, so
the decision procedure it licenses is a real one and not a classical
`Decidable` instance dressed up. There is no `sorry`, no `axiom`, no
`native_decide`, and no `#eval` standing in for a proof. -/

#print axioms EC1T017.Sub.refl
#print axioms EC1T017.exists_of_all_eq_false
#print axioms EC1T017.mem_nub
#print axioms EC1T017.mem_tagUniverse
#print axioms EC1T017.ownB_iff
#print axioms EC1T017.inhB_iff
#print axioms EC1T017.step_iff
#print axioms EC1T017.step_mono
#print axioms EC1T017.le_step
#print axioms EC1T017.iter_chain
#print axioms EC1T017.iter_below
#print axioms EC1T017.closed_of_fix
#print axioms EC1T017.iter_support
#print axioms EC1T017.cond_le_one
#print axioms EC1T017.rowCnt_le
#print axioms EC1T017.cnt_le
#print axioms EC1T017.cond_mono
#print axioms EC1T017.rowCnt_mono
#print axioms EC1T017.cnt_mono
#print axioms EC1T017.rowCnt_lt
#print axioms EC1T017.cnt_lt
#print axioms EC1T017.stab_of_stabB
#print axioms EC1T017.stab_forever
#print axioms EC1T017.stab_or_grow
#print axioms EC1T017.stabilises
#print axioms EC1T017.sol_fix
#print axioms EC1T017.sol_closed
#print axioms EC1T017.sol_least
#print axioms EC1T017.synthRow_adequate
#print axioms EC1T017.least_unique
#print axioms EC1T017.synthRow_unique
#print axioms EC1T017.synthRow_exists_unique
#print axioms EC1T017.synthAER_adequate
#print axioms EC1T017.synthAER_unique
#print axioms EC1T017.synthAER_exists_unique
#print axioms EC1T017.cyc_propagates_across_the_cycle
#print axioms EC1T017.cyc_handler_subtracts
#print axioms EC1T017.checked_aer_agrees
#print axioms EC1T017.checked_aer_agrees_needs_no_wf
#print axioms EC1T017.checked_declared_aer_agrees
#print axioms EC1T017.freeProg_row
#print axioms EC1T017.dangling_synthesized
#print axioms EC1T017.freeput_node_never_fails_admission
#print axioms EC1T017.freeput_refusal_is_the_put_refusal
#print axioms EC1T017.putWord_freeput_never_dangles
#print axioms EC1T017.freeput_never_refuses_dangling
#print axioms EC1T017.synthesized_E_is_may_not_must
#print axioms EC1T017.synthE_strictly_over_approximates
#print axioms EC1T017.functional_reading_makes_T017_a_projection
#print axioms EC1T017.functional_reading_makes_T016_premise_free
#print axioms EC1T017.SynthAER_refuses_the_empty_row
#print axioms EC1T017.SynthAER_refuses_an_over_approximation
#print axioms EC1T017.the_fold_is_the_alphabet
#print axioms EC1T017.fold_counts_unreachable_blocks
#print axioms EC1T017.fold_ignores_handler_subtraction
