import Cas.Core.Admission

/-!
# Effect Core v1 — `EC1-T011 check_complete`, implemented

Slice `EC1-S2`, the admission boundary. WORKSHOP ARTEFACT ONLY: nothing here is
proposed for `library/` or for `formal/effect-core-v1/`. Intended home of the
row is `formal/effect-core-v1/EffectCore/Admission/Check.lean`, which is today
an empty reserved boundary; this file does not write there.

Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/T011.lean
```

## What is proved

The DAG row is

```text
EC1-T011  check_complete : ProgramWF r -> exists p, check r = ok <a,p>
```

with `a` FREE. Section 6 refutes the universal closure of that `a` at this
carrier, so the row is stated here with the alphabet BOUND, and bound to the
synthesized value on the nose:

```text
check_complete : ProgramWF r -> exists p, check r = .ok <synthAER r, p>
```

which is strictly stronger than the existential closure (the DAG's other
reading), and is the form `EC1-T017` needs.

`check` here is a REAL, computable, first-error checker over four separately
named clauses, each with its own diagnostic-producing decision procedure, and
NONE of them mentions `ProgramWF`. That is what keeps the row from degenerating
into `Subtype.property`: `clauses_complete` is four independent reflection
lemmas composed over `Except`'s first-error sequencing, which is
`PROOF-DAG.md` section 16's named Checker route ("structural recursion plus
decidable per-clause reflection").

| Section | Content |
|---|---|
| 0 | Carrier: `RawProgram`, `AER`, `Diagnostic`. Minimal, first-order. |
| 1 | Row normalization and `synthAER`, declared independently of `check`. |
| 2 | Four clause judgments as ordinary propositions. |
| 3 | Four first-error diagnostic finders, each with a two-sided reflection pair. |
| 4 | `checkClauses`, `clauses_sound`, `clauses_complete`, `CheckedProgram`, `check`. |
| 5 | **`EC1-T011`.** Plus `check_sound` as a companion (that row belongs to another agent). |
| 6 | The free-`a` defect, refuted at this carrier. |
| 7 | **THE DECIDABILITY FINDING.** Clause 5 read semantically REFUTES `EC1-T011`. |
| 8 | The decision procedure the row hands back, constructively. |
| 9 | The shipped estate anchor, re-elaborated. |

## Scope, stated before the proofs

* FOUR clauses of `ALGEBRA.md` section 4.3's TWELVE are modeled: 1 `IdsWF`,
  10 `EntryWF`, 5 `HandlersWF` (under the DECLARED reading, see section 7),
  11 `AERWF`. Clauses 2, 3, 4, 6, 7, 8, 9, 12 are NOT modeled here. A theorem
  about a four-clause judgment is not a theorem about the twelve-clause one.
* The block body is ELIDED. `Block.ops` is a block's operation-key list, not a
  program. No second straight-line carrier is minted here: `ALGEBRA.md`
  section 4.2 rules that a real `Block` carries the existing `PProg` as its
  body, and this file mints no body carrier at all rather than a rival one.
* `AER` is modeled as the pair of rows `(E, R)` keyed by operation id. The
  value type `A` is elided.
* `normalizeRaw` is NOT applied on the way out: `CheckedProgram` stores the raw
  it was given, so `erase` is the stored field. This is the T014 scout's
  design (a). It sidesteps `EC1-CE030` entirely rather than paying its
  `NodupKeys` premise: the only normalized object in this carrier is the row,
  and rows are normalized INSIDE `synthAER`, strictly after nothing — the
  synthesizer is a pure function of the raw graph and the checker compares its
  output to the declared triple.
* No clause of the twelve is proved undecidable here, and none can be: Lean is
  classical, so every proposition is `Decidable` and undecidability is not
  expressible without a computability model. Section 7 proves the weaker, fully
  checkable fact instead, and it is enough to settle the row's warning.

No `sorry`, no `axiom`, no `native_decide`, no `#eval` for a claim.
`#print axioms` on every theorem at the foot.
-/

namespace EC1T011

/-! ## Section 0 — the carrier

`EC1-D020 RawProgram`, `EC1-D022 Diagnostic`, and the `AER` of `EC1-D005`, in
the smallest first-order form that carries the four clauses. -/

abbrev OpId := Nat
abbrev BlockId := Nat

/-- `EC1-D005` modeled as its two rows. `A` is elided; `E` and `R` are keyed
lists of operation ids. -/
structure AER where
  E : List OpId
  R : List OpId
deriving DecidableEq, Repr

/-- A graph node. `ops`/`reqs` are the operation and requirement KEYS the block
contributes; the sequential body is elided (see the scope note in the header).
`succ` are the block's exit edges. -/
structure Block where
  id   : BlockId
  ops  : List OpId
  reqs : List OpId
  succ : List BlockId
deriving DecidableEq, Repr

/-- `EC1-D020 RawProgram`. Deliberately admits ill-formed values: duplicate
ids, dangling edges, a missing entry, an unhandled operation and a wrong
declared triple are all REPRESENTABLE, per `ALGEBRA.md` lines 240-243. Without
that, `ProgramWF` would be a theorem rather than a judgment and the row would
be empty. -/
structure RawProgram where
  blocks   : List Block
  entry    : BlockId
  handlers : List OpId
  declared : AER
deriving DecidableEq, Repr

/-- `EC1-D022 Diagnostic`. A SINGLE first-error value carrying its payload —
`R16` part 1 and `EC1-CE031`. Section 6b shows the payload is not recoverable
from a clause code and a position, which is `EC1-T015`'s finding reproduced at
a second carrier. -/
inductive Diagnostic where
  | dupBlockId    (b : BlockId)
  | danglingSucc  (src : BlockId) (tgt : BlockId)
  | entryMissing  (b : BlockId)
  | handlerMissing (b : BlockId) (op : OpId) (found : Nat)
  | aerMismatch   (synth declared : AER)
deriving DecidableEq, Repr

/-! ## Section 1 — row normalization and the synthesizer

`synthAER` is declared here as an ordinary function of the raw graph. It is NOT
read off `check`; the scouts for `EC1-T011` and `EC1-T016` both showed that
defining it as `fun r a => exists p, check r = .ok <a,p>` makes `EC1-T016` a
tautology. Nothing below refers to `check`. -/

/-- Ordered insert with dedup: the row's canonical spelling. -/
def insertOp (x : OpId) : List OpId → List OpId
  | []      => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: insertOp x ys

/-- Row normalization. -/
def normRow : List OpId → List OpId
  | []      => []
  | x :: xs => insertOp x (normRow xs)

/-- Every element of a strictly increasing list is above `lo`, stated as a
bounded recursion so the insertion lemma needs no head-of-list reasoning. -/
def sortedFrom (lo : Nat) : List Nat → Bool
  | []      => true
  | x :: xs => decide (lo < x) && sortedFrom x xs

/-- Canonical spelling of a row: strictly increasing, hence duplicate-free. -/
def isCanonRow : List Nat → Bool
  | []      => true
  | x :: xs => sortedFrom x xs

theorem insertOp_sortedFrom {lo x : Nat} :
    ∀ {l : List Nat}, sortedFrom lo l = true → lo < x → sortedFrom lo (insertOp x l) = true := by
  intro l
  induction l generalizing lo with
  | nil => intro _ hlo; simp [insertOp, sortedFrom, hlo]
  | cons y ys ih =>
    intro h hlo
    simp [sortedFrom, Bool.and_eq_true] at h
    by_cases hxy : x < y
    · simp [insertOp, hxy, sortedFrom, hlo, h.2]
    · by_cases hxe : x = y
      · simp [insertOp, hxe, sortedFrom, h.1, h.2]
      · have hyx : y < x := Nat.lt_of_le_of_ne (Nat.not_lt.mp hxy) (fun hh => hxe hh.symm)
        simp only [insertOp, if_neg hxy, if_neg hxe, sortedFrom, Bool.and_eq_true,
          decide_eq_true_iff]
        exact ⟨h.1, ih h.2 hyx⟩

theorem insertOp_canon {x : Nat} :
    ∀ {l : List Nat}, isCanonRow l = true → isCanonRow (insertOp x l) = true := by
  intro l
  cases l with
  | nil => intro _; simp [insertOp, isCanonRow, sortedFrom]
  | cons y ys =>
    intro h
    have h' : sortedFrom y ys = true := by simpa [isCanonRow] using h
    by_cases hxy : x < y
    · simp [insertOp, hxy, isCanonRow, sortedFrom, h']
    · by_cases hxe : x = y
      · simp [insertOp, hxe, isCanonRow, h']
      · have hyx : y < x := Nat.lt_of_le_of_ne (Nat.not_lt.mp hxy) (fun hh => hxe hh.symm)
        simp only [insertOp, if_neg hxy, if_neg hxe, isCanonRow]
        exact insertOp_sortedFrom h' hyx

/-- Row normalization always produces the canonical spelling. Recorded because
it settles a structural question about `ALGEBRA.md` section 4.3 that the packet
states as a separate clause: clause 3's canonicity half is DERIVABLE from
clause 11 once the synthesizer normalizes, so the twelve clauses are not
independent. -/
theorem normRow_canon : ∀ l : List OpId, isCanonRow (normRow l) = true := by
  intro l
  induction l with
  | nil => simp [normRow, isCanonRow]
  | cons x xs ih => exact insertOp_canon ih

def allOps : List Block → List OpId
  | []      => []
  | b :: bs => b.ops ++ allOps bs

def allReqs : List Block → List OpId
  | []      => []
  | b :: bs => b.reqs ++ allReqs bs

/-- The synthesizer. A static MAY summary over the DECLARED blocks: it is not
a runtime trace summary, and section 7 records what that costs. -/
def synthAER (r : RawProgram) : AER :=
  { E := normRow (allOps r.blocks), R := normRow (allReqs r.blocks) }

/-- The synthesized triple is always canonically spelled. -/
theorem synthAER_canon (r : RawProgram) :
    isCanonRow (synthAER r).E = true ∧ isCanonRow (synthAER r).R = true :=
  ⟨normRow_canon _, normRow_canon _⟩

/-! ## Section 2 — the clause judgments

Four separately named propositions. Each is written in ordinary logical form,
with NO reference to any decision procedure — otherwise the reflection lemmas
of section 3 would be `Iff.rfl` and `EC1-T011` would be empty. -/

/-- `i` names a declared block. -/
def Declared (bs : List Block) (i : BlockId) : Prop := ∃ b, b ∈ bs ∧ b.id = i

/-- Block ids are duplicate-free. -/
def NoDupIds : List Block → Prop
  | []      => True
  | b :: bs => (∀ c, c ∈ bs → c.id ≠ b.id) ∧ NoDupIds bs

/-- Clause 1 of `ALGEBRA.md` section 4.3, `IdsWF`: tables duplicate-free and
every reference resolves. -/
def IdsWF (r : RawProgram) : Prop :=
  NoDupIds r.blocks ∧ ∀ b, b ∈ r.blocks → ∀ s, s ∈ b.succ → Declared r.blocks s

/-- Clause 10, `EntryWF`, entry-resolution half. -/
def EntryWF (r : RawProgram) : Prop := Declared r.blocks r.entry

/-- Clause 5, `HandlersWF`, under the DECLARED reading: exactly one clause for
every operation of every DECLARED block. Section 7 is about the difference
between this and the packet's word "reachable". -/
def HandlersWF (r : RawProgram) : Prop :=
  ∀ b, b ∈ r.blocks → ∀ op, op ∈ b.ops → r.handlers.count op = 1

/-- Clause 11, `AERWF`: the synthesized triple is the declared one. -/
def AERWF (r : RawProgram) : Prop := synthAER r = r.declared

/-- `EC1-D021 ProgramWF`, four clauses in the frozen checker order. -/
def ProgramWF (r : RawProgram) : Prop :=
  IdsWF r ∧ EntryWF r ∧ HandlersWF r ∧ AERWF r

/-! ## Section 3 — first-error diagnostic finders, with two-sided reflection

Each finder returns `none` exactly when its clause holds, and otherwise a
diagnostic carrying its witness. The `_none_iff` lemmas are the per-clause
reflection the section 16 route names; they are where `EC1-T011`'s content
lives. -/

def declaredB (bs : List Block) (i : BlockId) : Bool := bs.any (fun b => b.id == i)

theorem declaredB_iff {bs : List Block} {i : BlockId} :
    declaredB bs i = true ↔ Declared bs i := by
  simp [declaredB, Declared, List.any_eq_true]

theorem declaredB_false_iff {bs : List Block} {i : BlockId} :
    declaredB bs i = false ↔ ∀ c, c ∈ bs → c.id ≠ i := by
  simp [declaredB, List.any_eq_false]

/-- Clause 1, first half. -/
def firstDupId : List Block → Option BlockId
  | []      => none
  | b :: bs => if declaredB bs b.id then some b.id else firstDupId bs

theorem firstDupId_none_iff : ∀ bs : List Block, firstDupId bs = none ↔ NoDupIds bs := by
  intro bs
  induction bs with
  | nil => simp [firstDupId, NoDupIds]
  | cons b bs ih =>
    cases hb : declaredB bs b.id with
    | true =>
      have h1 : firstDupId (b :: bs) ≠ none := by simp [firstDupId, hb]
      constructor
      · intro hc; exact absurd hc h1
      · intro hnd
        have := declaredB_false_iff.mpr hnd.1
        rw [hb] at this; exact absurd this (by simp)
    | false =>
      have h1 : firstDupId (b :: bs) = firstDupId bs := by simp [firstDupId, hb]
      rw [h1, ih]
      exact ⟨fun hh => ⟨declaredB_false_iff.mp hb, hh⟩, fun hh => hh.2⟩

/-- Clause 1, second half: the first exit edge that does not resolve. -/
def firstUnresolved (bs : List Block) : List BlockId → Option BlockId
  | []      => none
  | s :: ss => if declaredB bs s then firstUnresolved bs ss else some s

theorem firstUnresolved_none_iff {bs : List Block} :
    ∀ ss : List BlockId, firstUnresolved bs ss = none ↔ ∀ s, s ∈ ss → Declared bs s := by
  intro ss
  induction ss with
  | nil => simp [firstUnresolved]
  | cons s ss ih =>
    cases hb : declaredB bs s with
    | true =>
      have h1 : firstUnresolved bs (s :: ss) = firstUnresolved bs ss := by
        simp [firstUnresolved, hb]
      rw [h1, ih]
      constructor
      · intro hh t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact declaredB_iff.mp hb
        · exact hh t ht'
      · intro hh t ht; exact hh t (List.mem_cons.mpr (Or.inr ht))
    | false =>
      have h1 : firstUnresolved bs (s :: ss) ≠ none := by simp [firstUnresolved, hb]
      constructor
      · intro hc; exact absurd hc h1
      · intro hh
        have := declaredB_iff.mpr (hh s (List.mem_cons.mpr (Or.inl rfl)))
        rw [hb] at this; exact absurd this (by simp)

def firstDangling (bs : List Block) : List Block → Option (BlockId × BlockId)
  | []      => none
  | b :: cs =>
    match firstUnresolved bs b.succ with
    | some s => some (b.id, s)
    | none   => firstDangling bs cs

theorem firstDangling_none_iff {bs : List Block} :
    ∀ cs : List Block,
      firstDangling bs cs = none ↔ ∀ b, b ∈ cs → ∀ s, s ∈ b.succ → Declared bs s := by
  intro cs
  induction cs with
  | nil => simp [firstDangling]
  | cons b cs ih =>
    cases hu : firstUnresolved bs b.succ with
    | some s =>
      have h1 : firstDangling bs (b :: cs) ≠ none := by simp [firstDangling, hu]
      constructor
      · intro hc; exact absurd hc h1
      · intro hh
        have : firstUnresolved bs b.succ = none :=
          (firstUnresolved_none_iff b.succ).mpr (hh b (List.mem_cons.mpr (Or.inl rfl)))
        rw [hu] at this; exact absurd this (by simp)
    | none =>
      have h1 : firstDangling bs (b :: cs) = firstDangling bs cs := by
        simp [firstDangling, hu]
      rw [h1, ih]
      constructor
      · intro hh c hc s hs
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact (firstUnresolved_none_iff c.succ).mp hu s hs
        · exact hh c hc' s hs
      · intro hh c hc s hs; exact hh c (List.mem_cons.mpr (Or.inr hc)) s hs

/-- Clause 1's diagnostic finder. -/
def idsDiag (r : RawProgram) : Option Diagnostic :=
  match firstDupId r.blocks with
  | some i => some (.dupBlockId i)
  | none =>
    match firstDangling r.blocks r.blocks with
    | some (src, tgt) => some (.danglingSucc src tgt)
    | none            => none

theorem idsDiag_none_iff (r : RawProgram) : idsDiag r = none ↔ IdsWF r := by
  cases hd : firstDupId r.blocks with
  | some i =>
    have h1 : idsDiag r ≠ none := by simp [idsDiag, hd]
    constructor
    · intro hc; exact absurd hc h1
    · intro hh
      have := (firstDupId_none_iff r.blocks).mpr hh.1
      rw [hd] at this; exact absurd this (by simp)
  | none =>
    cases hg : firstDangling r.blocks r.blocks with
    | some p =>
      obtain ⟨src, tgt⟩ := p
      have h1 : idsDiag r ≠ none := by simp [idsDiag, hd, hg]
      constructor
      · intro hc; exact absurd hc h1
      · intro hh
        have := (firstDangling_none_iff r.blocks).mpr hh.2
        rw [hg] at this; exact absurd this (by simp)
    | none =>
      have h1 : idsDiag r = none := by simp [idsDiag, hd, hg]
      rw [h1]
      exact ⟨fun _ => ⟨(firstDupId_none_iff r.blocks).mp hd,
                        (firstDangling_none_iff r.blocks).mp hg⟩, fun _ => rfl⟩

/-- Clause 10's diagnostic finder. -/
def entryDiag (r : RawProgram) : Option Diagnostic :=
  if declaredB r.blocks r.entry then none else some (.entryMissing r.entry)

theorem entryDiag_none_iff (r : RawProgram) : entryDiag r = none ↔ EntryWF r := by
  cases hb : declaredB r.blocks r.entry with
  | true =>
    have h1 : entryDiag r = none := by simp [entryDiag, hb]
    rw [h1]
    exact ⟨fun _ => declaredB_iff.mp hb, fun _ => rfl⟩
  | false =>
    have h1 : entryDiag r ≠ none := by simp [entryDiag, hb]
    constructor
    · intro hc; exact absurd hc h1
    · intro hh
      have := declaredB_iff.mpr hh
      rw [hb] at this; exact absurd this (by simp)

/-- Clause 5's diagnostic finder, declared reading. -/
def firstUnhandled (hs : List OpId) : List OpId → Option (OpId × Nat)
  | []        => none
  | op :: ops => if hs.count op = 1 then firstUnhandled hs ops else some (op, hs.count op)

theorem firstUnhandled_none_iff {hs : List OpId} :
    ∀ ops : List OpId, firstUnhandled hs ops = none ↔ ∀ op, op ∈ ops → hs.count op = 1 := by
  intro ops
  induction ops with
  | nil => simp [firstUnhandled]
  | cons op ops ih =>
    by_cases h : hs.count op = 1
    · have h1 : firstUnhandled hs (op :: ops) = firstUnhandled hs ops := by
        simp [firstUnhandled, h]
      rw [h1, ih]
      constructor
      · intro hh t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact h
        · exact hh t ht'
      · intro hh t ht; exact hh t (List.mem_cons.mpr (Or.inr ht))
    · have h1 : firstUnhandled hs (op :: ops) ≠ none := by simp [firstUnhandled, h]
      constructor
      · intro hc; exact absurd hc h1
      · intro hh; exact absurd (hh op (List.mem_cons.mpr (Or.inl rfl))) h

def firstUnhandledBlock (hs : List OpId) : List Block → Option (BlockId × OpId × Nat)
  | []      => none
  | b :: bs =>
    match firstUnhandled hs b.ops with
    | some (op, n) => some (b.id, op, n)
    | none         => firstUnhandledBlock hs bs

theorem firstUnhandledBlock_none_iff {hs : List OpId} :
    ∀ bs : List Block,
      firstUnhandledBlock hs bs = none ↔ ∀ b, b ∈ bs → ∀ op, op ∈ b.ops → hs.count op = 1 := by
  intro bs
  induction bs with
  | nil => simp [firstUnhandledBlock]
  | cons b bs ih =>
    cases hu : firstUnhandled hs b.ops with
    | some p =>
      obtain ⟨op, n⟩ := p
      have h1 : firstUnhandledBlock hs (b :: bs) ≠ none := by simp [firstUnhandledBlock, hu]
      constructor
      · intro hc; exact absurd hc h1
      · intro hh
        have := (firstUnhandled_none_iff b.ops).mpr (hh b (List.mem_cons.mpr (Or.inl rfl)))
        rw [hu] at this; exact absurd this (by simp)
    | none =>
      have h1 : firstUnhandledBlock hs (b :: bs) = firstUnhandledBlock hs bs := by
        simp [firstUnhandledBlock, hu]
      rw [h1, ih]
      constructor
      · intro hh c hc op hop
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact (firstUnhandled_none_iff c.ops).mp hu op hop
        · exact hh c hc' op hop
      · intro hh c hc op hop; exact hh c (List.mem_cons.mpr (Or.inr hc)) op hop

def handlersDiag (r : RawProgram) : Option Diagnostic :=
  match firstUnhandledBlock r.handlers r.blocks with
  | some (bid, op, n) => some (.handlerMissing bid op n)
  | none              => none

theorem handlersDiag_none_iff (r : RawProgram) : handlersDiag r = none ↔ HandlersWF r := by
  cases hu : firstUnhandledBlock r.handlers r.blocks with
  | some p =>
    obtain ⟨bid, op, n⟩ := p
    have h1 : handlersDiag r ≠ none := by simp [handlersDiag, hu]
    constructor
    · intro hc; exact absurd hc h1
    · intro hh
      have := (firstUnhandledBlock_none_iff r.blocks).mpr hh
      rw [hu] at this; exact absurd this (by simp)
  | none =>
    have h1 : handlersDiag r = none := by simp [handlersDiag, hu]
    rw [h1]
    exact ⟨fun _ => (firstUnhandledBlock_none_iff r.blocks).mp hu, fun _ => rfl⟩

/-- Clause 11's diagnostic finder. -/
def aerDiag (r : RawProgram) : Option Diagnostic :=
  if synthAER r = r.declared then none else some (.aerMismatch (synthAER r) r.declared)

theorem aerDiag_none_iff (r : RawProgram) : aerDiag r = none ↔ AERWF r := by
  unfold aerDiag AERWF
  by_cases h : synthAER r = r.declared
  · simp [h]
  · simp [h]

/-! ## Section 4 — the checker

First-error over ONE frozen clause order (`R16`, `EC1-CE031`). Note what
`check` is NOT: it is not `dite (decide (ProgramWF r))`. It is a match over
four independent finders, none of which mentions `ProgramWF`. -/

/-- The clause layer. Decides the RAW input, in the frozen order
1 `IdsWF`, 10 `EntryWF`, 5 `HandlersWF`, 11 `AERWF`. -/
def checkClauses (r : RawProgram) : Except Diagnostic Unit :=
  match idsDiag r with
  | some d => .error d
  | none =>
    match entryDiag r with
    | some d => .error d
    | none =>
      match handlersDiag r with
      | some d => .error d
      | none =>
        match aerDiag r with
        | some d => .error d
        | none   => .ok ()

/-- First-error soundness of the clause layer. -/
theorem clauses_sound {r : RawProgram} {u : Unit} (h : checkClauses r = .ok u) :
    ProgramWF r := by
  unfold checkClauses at h
  cases hi : idsDiag r with
  | some d => rw [hi] at h; exact absurd h (by simp)
  | none =>
    cases he : entryDiag r with
    | some d => rw [hi, he] at h; exact absurd h (by simp)
    | none =>
      cases hh : handlersDiag r with
      | some d => rw [hi, he, hh] at h; exact absurd h (by simp)
      | none =>
        cases ha : aerDiag r with
        | some d => rw [hi, he, hh, ha] at h; exact absurd h (by simp)
        | none =>
          exact ⟨(idsDiag_none_iff r).mp hi, (entryDiag_none_iff r).mp he,
                 (handlersDiag_none_iff r).mp hh, (aerDiag_none_iff r).mp ha⟩

/-- Acceptance completeness of the clause layer. THIS is `EC1-T011`'s content:
four independent reflection lemmas composed over first-error sequencing. -/
theorem clauses_complete {r : RawProgram} (h : ProgramWF r) : checkClauses r = .ok () := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold checkClauses
  rw [(idsDiag_none_iff r).mpr h1, (entryDiag_none_iff r).mpr h2,
      (handlersDiag_none_iff r).mpr h3, (aerDiag_none_iff r).mpr h4]

/-- `EC1-D023 CheckedProgram`. Stores the raw it was given plus evidence, and
pins the index to the synthesized value. -/
structure CheckedProgram (aer : AER) where
  raw   : RawProgram
  wf    : ProgramWF raw
  aerOk : synthAER raw = aer

/-- `EC1-D025 erase`. -/
def erase {aer : AER} (p : CheckedProgram aer) : RawProgram := p.raw

/-- `EC1-D024 check`. Computable; `Except` by `R15`/`EC1-CE033`. -/
def check (r : RawProgram) : Except Diagnostic (Sigma CheckedProgram) :=
  match hc : checkClauses r with
  | .error d => .error d
  | .ok _    => .ok ⟨synthAER r, { raw := r, wf := clauses_sound hc, aerOk := rfl }⟩

/-! ## Section 5 — the row -/

/-- **`EC1-T011 check_complete`.** The alphabet is BOUND, and bound to
`synthAER r` on the nose — strictly stronger than the DAG row's existential
reading (section 6), and the form `EC1-T017` needs. -/
theorem check_complete {r : RawProgram} (h : ProgramWF r) :
    ∃ p : CheckedProgram (synthAER r), check r = .ok ⟨synthAER r, p⟩ := by
  have hc : checkClauses r = .ok () := clauses_complete h
  unfold check
  split
  · next d hd => rw [hc] at hd; exact absurd hd (by simp)
  · next u hu => exact ⟨_, rfl⟩

/-- The DAG row's existential closure, as a corollary. -/
theorem check_complete_dag {r : RawProgram} (h : ProgramWF r) :
    ∃ (aer : AER) (p : CheckedProgram aer), check r = .ok ⟨aer, p⟩ :=
  let ⟨p, hp⟩ := check_complete h; ⟨synthAER r, p, hp⟩

/-- COMPANION, NOT MY ROW: `EC1-T010` belongs to another agent in this slice.
It is proved here only because without it `EC1-T011` is satisfied by a checker
that accepts everything, so the pair is what has content. -/
theorem check_ok_raw {r : RawProgram} {x : Sigma CheckedProgram} (h : check r = .ok x) :
    x.2.raw = r := by
  unfold check at h
  split at h
  · next d hd => exact absurd h (by simp)
  · next u hu => cases h; rfl

/-- COMPANION, NOT MY ROW (`EC1-T010`). -/
theorem check_sound {r : RawProgram} {aer : AER} {p : CheckedProgram aer}
    (h : check r = .ok ⟨aer, p⟩) : ProgramWF r :=
  check_ok_raw h ▸ p.wf

/-! ## Section 6 — the free `a` in the DAG signature

`check_complete : ProgramWF r -> exists p, check r = ok <a,p>` leaves `a` free.
Under Lean's convention a free variable is universally bound at the front. That
reading is FALSE at this carrier. -/

/-- A well-formed program: one block, no ops, no edges, empty declared rows. -/
def goodProgram : RawProgram :=
  { blocks := [{ id := 0, ops := [], reqs := [], succ := [] }], entry := 0,
    handlers := [], declared := { E := [], R := [] } }

theorem goodProgram_wf : ProgramWF goodProgram := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact ⟨fun c hc => absurd hc (by simp), trivial⟩
  · intro b hb s hs
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd hs (by simp)
    · exact absurd hb' (by simp)
  · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), rfl⟩
  · intro b hb op hop
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd hop (by simp)
    · exact absurd hb' (by simp)
  · rfl

theorem goodProgram_synth : synthAER goodProgram = { E := [], R := [] } := rfl

/-- **The universal closure of `a` is false.** A `check` answer names ONE
alphabet. Any `AER` other than the synthesized one is not returned. -/
theorem forall_aer_closure_is_false :
    ¬ ∀ (r : RawProgram), ProgramWF r →
        ∀ aer : AER, ∃ p : CheckedProgram aer, check r = .ok ⟨aer, p⟩ := by
  intro hall
  obtain ⟨p, hp⟩ := hall goodProgram goodProgram_wf { E := [7], R := [] }
  obtain ⟨q, hq⟩ := check_complete goodProgram_wf
  rw [hq] at hp
  injection hp with hs
  have hfst : synthAER goodProgram = { E := [7], R := [] } := congrArg Sigma.fst hs
  exact absurd hfst (by decide)

/-! ### Section 6b — the diagnostic is not a function of clause and position

`EC1-T015`'s finding, reproduced at this carrier: two programs reject at the
same block, the same clause and the same operation, with DIFFERENT payloads.
So `Diagnostic` may not be spelled as a clause code plus a path. -/

def unhandledA : RawProgram :=
  { blocks := [{ id := 0, ops := [9], reqs := [], succ := [] }], entry := 0,
    handlers := [], declared := { E := [9], R := [] } }

def unhandledB : RawProgram :=
  { blocks := [{ id := 0, ops := [9], reqs := [], succ := [] }], entry := 0,
    handlers := [9, 9], declared := { E := [9], R := [] } }

theorem diagnostic_payload_is_not_clause_plus_position :
    checkClauses unhandledA = .error (.handlerMissing 0 9 0)
      ∧ checkClauses unhandledB = .error (.handlerMissing 0 9 2)
      ∧ (Diagnostic.handlerMissing 0 9 0) ≠ (Diagnostic.handlerMissing 0 9 2) := by
  refine ⟨rfl, rfl, by simp⟩

/-! ## Section 7 — THE DECIDABILITY FINDING

The brief's warning: `EC1-T011` is PROHIBITED if any `ProgramWF` clause is
silently changed to an undecidable semantic property. This section makes that
warning a checked fact at a concrete carrier rather than lane discipline.

`ALGEBRA.md` line 305 spells clause 5 as "exactly one typed clause for every
REACHABLE operation". Section 2 above implements the DECLARED reading. The two
differ, and the difference is not a matter of proof difficulty: the syntactic
clause is STRICTLY STRONGER, so it keeps `EC1-T010` and KILLS `EC1-T011`.

No semantics is committed to. A `Semantics` is any assignment of reached blocks
satisfying the single fact every run semantics of a block graph supplies: what
is reached is declared. -/

structure Semantics where
  Reached : RawProgram → BlockId → Prop
  reached_declared : ∀ r b, Reached r b → Declared r.blocks b

/-- Clause 5 under the SEMANTIC reading. -/
def HandlersWFsem (S : Semantics) (r : RawProgram) : Prop :=
  ∀ b, b ∈ r.blocks → S.Reached r b.id → ∀ op, op ∈ b.ops → r.handlers.count op = 1

def ProgramWFsem (S : Semantics) (r : RawProgram) : Prop :=
  IdsWF r ∧ EntryWF r ∧ HandlersWFsem S r ∧ AERWF r

/-- The syntactic judgment is STRICTLY STRONGER, so `EC1-T010` survives the
semantic reading: a checker complete for the declared clause is still sound for
the semantic one. This is the half that misleads. -/
theorem syn_implies_sem (S : Semantics) {r : RawProgram} (h : ProgramWF r) :
    ProgramWFsem S r :=
  ⟨h.1, h.2.1, fun b hb _ op hop => h.2.2.1 b hb op hop, h.2.2.2⟩

/-- A legitimate semantics: only the entry block runs. Realized by any program
whose entry returns immediately. -/
def entryOnly : Semantics where
  Reached := fun r b => b = r.entry ∧ Declared r.blocks b
  reached_declared := fun _ _ h => h.2

/-- A program with a statically-present, semantically-dead block whose
operation has no handler clause. -/
def deadBlockProgram : RawProgram :=
  { blocks := [{ id := 0, ops := [],  reqs := [], succ := [] },
               { id := 1, ops := [9], reqs := [], succ := [] }],
    entry := 0, handlers := [], declared := { E := [9], R := [] } }

theorem deadBlockProgram_sem_wf : ProgramWFsem entryOnly deadBlockProgram := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨fun c hc => ?_, ⟨fun c hc => absurd hc (by simp), trivial⟩⟩
    rcases List.mem_cons.mp hc with rfl | hc'
    · simp
    · exact absurd hc' (by simp)
  · intro b hb s hs
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd hs (by simp)
    · rcases List.mem_cons.mp hb' with rfl | hb''
      · exact absurd hs (by simp)
      · exact absurd hb'' (by simp)
  · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), rfl⟩
  · intro b hb hre op hop
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd hop (by simp)
    · rcases List.mem_cons.mp hb' with rfl | hb''
      · exact absurd hre.1 (by decide)
      · exact absurd hb'' (by simp)
  · rfl

/-- **`EC1-T011` IS FALSE FOR THE SEMANTIC READING OF CLAUSE 5.** The program
above satisfies the semantic judgment and the checker REJECTS it, naming the
clause and the dead block. No approximation inside `check` can repair this:
by section 8 a sound and complete checker decides its predicate, so the
syntactic reading must be written into `ProgramWF` ITSELF. -/
theorem semantic_clause_refutes_T011 :
    ProgramWFsem entryOnly deadBlockProgram
      ∧ check deadBlockProgram = .error (.handlerMissing 1 9 0)
      ∧ ¬ ∃ (aer : AER) (p : CheckedProgram aer),
            check deadBlockProgram = .ok ⟨aer, p⟩ := by
  refine ⟨deadBlockProgram_sem_wf, rfl, ?_⟩
  rintro ⟨aer, p, hp⟩
  rw [show check deadBlockProgram = .error (.handlerMissing 1 9 0) from rfl] at hp
  exact absurd hp (by simp)

/-- The general shape, so the witness is not read as an accident of this one
program. A checker that decides the STRICTLY stronger judgment `P` stays SOUND
for the weaker `Q` — `EC1-T010` survives — and REJECTS a witness of `Q`, so
`EC1-T011` for `Q` fails. Both halves at once, which is the asymmetry that
makes this failure mode easy to miss. -/
theorem strict_strengthening_keeps_soundness_kills_completeness
    {P Q : RawProgram → Prop} (hstrong : ∀ r, P r → Q r)
    {r₀ : RawProgram} (hq : Q r₀) (hnp : ¬ P r₀)
    (chk : RawProgram → Bool) (hsound : ∀ r, chk r = true → P r) :
    (∀ r, chk r = true → Q r) ∧ Q r₀ ∧ chk r₀ = false := by
  refine ⟨fun r h => hstrong r (hsound r h), hq, ?_⟩
  cases h : chk r₀ with
  | false => rfl
  | true  => exact absurd (hsound r₀ h) hnp

/-! ### Section 7b — the two vacuity guards `EC1-T011` needs

A completeness row is empty if its premise is never satisfied, and free if its
premise is always satisfied. Both are excluded here, and the second is excluded
by a program the checker actually rejects. -/

/-- `ProgramWF` is not everywhere false: `EC1-T011`'s premise is inhabited.
(`goodProgram_wf`, restated here as the guard it is.) -/
theorem programWF_is_inhabited : ProgramWF goodProgram := goodProgram_wf

/-- `ProgramWF` is not everywhere true: the checker rejects, so `EC1-T011` is
not satisfied by an accept-everything checker. -/
theorem programWF_is_not_universal : ¬ ProgramWF deadBlockProgram := by
  intro h
  obtain ⟨p, hp⟩ := check_complete h
  rw [show check deadBlockProgram = .error (.handlerMissing 1 9 0) from rfl] at hp
  exact absurd hp (by simp)

/-- Computational receipt. `check` REDUCES in the kernel on closed inputs, with
no `Decidable (ProgramWF _)` instance anywhere in scope — both equations are
`rfl`. A checker written as `dite (decide (ProgramWF r))` could not do this,
and `EC1-T011` for such a checker would be `Subtype.property`. This is the
kernel-visible form of the anti-vacuity condition the `EC1-T010` scout named. -/
theorem check_computes :
    checkClauses goodProgram = .ok ()
      ∧ checkClauses deadBlockProgram = .error (.handlerMissing 1 9 0) :=
  ⟨rfl, rfl⟩

/-! ## Section 8 — the decision procedure the row hands back

The DAG lists "decidability of every WF clause" as a DEPENDENCY of `EC1-T011`.
At the level of the row that is the wrong direction: soundness plus acceptance
completeness CONSTRUCT the decision, with no classical input. The receipt at
the foot is the gate: if `Classical.choice` ever appears under `check_complete`,
the checker has stopped being a decision procedure. -/

/-- Constructive: the `ok` arm supplies the proof, the `error` arm refutes,
because completeness would have forced an `ok`. -/
def decideOfChecker {P : RawProgram → Prop}
    (chk : RawProgram → Except Diagnostic (Sigma CheckedProgram))
    (sound : ∀ r x, chk r = .ok x → P r)
    (complete : ∀ r, P r → ∃ x, chk r = .ok x)
    (r : RawProgram) : Decidable (P r) :=
  match h : chk r with
  | .ok x    => isTrue (sound r x h)
  | .error _ =>
    isFalse (fun hp => by
      obtain ⟨x, hx⟩ := complete r hp
      rw [h] at hx
      exact absurd hx (by simp))

/-- `ProgramWF` is decided BY THE CHECKER, not by an ambient instance. Written
as a `def` and not an `instance`, so instance resolution never routes a clause
goal through a whole-program check — the discipline of
`Cas/IR/Reach.lean:550 decidableReach`. -/
def decidableProgramWF (r : RawProgram) : Decidable (ProgramWF r) :=
  decideOfChecker check (fun _ x h => check_ok_raw h ▸ x.2.wf)
    (fun _ hp => let ⟨_p, hp'⟩ := check_complete hp; ⟨_, hp'⟩) r

/-- And the error branch decides exactly the complement — `EC1-T012`'s shape,
NOT MY ROW, recorded only because it is free here and the coordinator should
see that this checker supports it. -/
theorem check_error_iff (r : RawProgram) :
    (∃ d, check r = .error d) ↔ ¬ ProgramWF r := by
  constructor
  · rintro ⟨d, hd⟩ hwf
    obtain ⟨_p, hp⟩ := check_complete hwf
    rw [hd] at hp; exact absurd hp (by simp)
  · intro hn
    cases h : check r with
    | ok x    => exact absurd (check_ok_raw h ▸ x.2.wf) hn
    | error d => exact ⟨d, rfl⟩

/-! ## Section 9 — the shipped estate anchor

`Cas/Core/Admission.lean` is the estate's only fail-fast checker of this family
and its `checkRefs_ok_iff` is the one-clause instance of exactly the pair
above: `.mp` is `EC1-T010`, `.mpr` is `EC1-T011`. Re-elaborated so the lineage
of the shape is checked and not merely cited. -/

namespace EstateAnchor

open Cas

/-- `EC1-T011`'s direction at the estate carrier. -/
theorem checkRefs_acceptComplete {σ : Store} {rs : List Ref} (h : RefsOk σ rs) :
    checkRefs σ rs = .ok () :=
  checkRefs_ok_iff.mpr h

/-- `EC1-T010`'s direction. Recorded together so the mis-assignment the
`EC1-T011` scout reported stays visible: `checkRefs_complete` is REJECTION
completeness and anchors `EC1-T012`, not this row. -/
theorem checkRefs_sound {σ : Store} {rs : List Ref} (h : checkRefs σ rs = .ok ()) :
    RefsOk σ rs :=
  checkRefs_ok_iff.mp h

end EstateAnchor

end EC1T011

/-! ## Kernel receipts -/

#print axioms EC1T011.insertOp_sortedFrom
#print axioms EC1T011.insertOp_canon
#print axioms EC1T011.normRow_canon
#print axioms EC1T011.synthAER_canon
#print axioms EC1T011.declaredB_iff
#print axioms EC1T011.declaredB_false_iff
#print axioms EC1T011.firstDupId_none_iff
#print axioms EC1T011.firstUnresolved_none_iff
#print axioms EC1T011.firstDangling_none_iff
#print axioms EC1T011.idsDiag_none_iff
#print axioms EC1T011.entryDiag_none_iff
#print axioms EC1T011.firstUnhandled_none_iff
#print axioms EC1T011.firstUnhandledBlock_none_iff
#print axioms EC1T011.handlersDiag_none_iff
#print axioms EC1T011.aerDiag_none_iff
#print axioms EC1T011.clauses_sound
#print axioms EC1T011.clauses_complete
#print axioms EC1T011.check_complete
#print axioms EC1T011.check_complete_dag
#print axioms EC1T011.check_ok_raw
#print axioms EC1T011.check_sound
#print axioms EC1T011.goodProgram_wf
#print axioms EC1T011.forall_aer_closure_is_false
#print axioms EC1T011.diagnostic_payload_is_not_clause_plus_position
#print axioms EC1T011.syn_implies_sem
#print axioms EC1T011.deadBlockProgram_sem_wf
#print axioms EC1T011.semantic_clause_refutes_T011
#print axioms EC1T011.strict_strengthening_keeps_soundness_kills_completeness
#print axioms EC1T011.programWF_is_inhabited
#print axioms EC1T011.programWF_is_not_universal
#print axioms EC1T011.check_computes
#print axioms EC1T011.decideOfChecker
#print axioms EC1T011.decidableProgramWF
#print axioms EC1T011.check_error_iff
#print axioms EC1T011.EstateAnchor.checkRefs_acceptComplete
#print axioms EC1T011.EstateAnchor.checkRefs_sound
