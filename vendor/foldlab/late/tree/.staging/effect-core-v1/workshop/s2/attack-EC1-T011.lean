import Cas.Core.Admission

/-!
# BREAKER attack witnesses against `EC1-T011 check_complete`

Target: `.staging/effect-core-v1/workshop/s2/T011.lean`, claimed PROVED-WEAKER.
Role: refutation, not confirmation. Stage:
`.claude/skills/lean/workflows/lean-assurance-review/SKILL.md`.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/attack-EC1-T011.lean
```

## Method

Sections 0-9 below are a VERBATIM COPY of `T011.lean` lines 85-859 (its whole
`namespace EC1T011` body), reproduced so the attacks below bear on exactly the
objects the target defines, byte for byte, and not on a paraphrase. Nothing in
the copy is edited. The attacks are section A, in a separate namespace, and
every one of them is a new theorem with its own kernel receipt.

## What the attacks establish

| Attack | Result |
|---|---|
| A1 | The report's "holds for EVERY semantics ... which is all of them" is FALSE. `allDeclared` is a `Semantics` under which `deadBlockProgram` is NOT semantically well-formed. The section-7 refutation is EXISTENTIAL in the semantics. |
| A2 | `entryOnly` is not successor-closed, so it is not a semantics of the block graph. The finding is REPAIRED: it survives at `succClosed`, a genuinely successor-closed reachability. |
| A3 | Clause 5 has a SECOND, UNDECLARED strengthening. `ALGEBRA.md:305` reads "... for every reachable operation OR A NAMED PARENT DELEGATION". The target drops the disjunct. For EVERY delegation reading under which op 9 of `unhandledA` is delegated, `EC1-T011` fails again — at the ENTRY block, so this defect is independent of the reachability question the target reports. |
| A4 | `EC1-F03` is not red. A raw program carrying BOTH a duplicated operation id and a duplicated handler id is ACCEPTED by `check`. |
| A5 | `EC1-F81` stays red. R16 upheld: the later condemning clause is reachable as a finder, and `check` refuses to report it. |
| A6 | `EC1-F01` and `EC1-F09` are red, at the exact edge / with both rows in the payload. |
| A7 | This carrier makes `EC1-T016` and `EC1-T017` CONTENTLESS — the same vacuity the target diagnoses for `EC1-T010`, arriving from the pinning the report recommends adopting upstream. `T016` does not even use its hypothesis. |
| A8 | The four clauses cover THREE of `ALGEBRA.md`'s twelve, not four: `EntryWF` here is reference resolution (clause 1) and models neither half of clause 10 (`ALGEBRA.md:314-315`). |

No `sorry`, no `axiom`, no `native_decide`, no `#eval` for a claim.
`#print axioms` on every attack theorem at the foot.
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

/-! # Section A — THE ATTACKS

Everything above this line is the target file, verbatim. Everything below is
new. -/

namespace AttackT011

open EC1T011

/-! ## A1 — the semantic refutation is EXISTENTIAL in the semantics

The target's report says of `semantic_clause_refutes_T011`:

> The refutation therefore holds for EVERY semantics of the block graph
> satisfying that one fact, which is all of them.

That is false, and the theorem in the file does not say it: the file's theorem
is stated at `entryOnly` alone. Here is a `Semantics` — satisfying the same
single fact `Reached r b -> Declared r.blocks b` — at which `deadBlockProgram`
is NOT semantically well-formed, so no refutation is available there. -/

/-- Every declared block runs. Satisfies `reached_declared` on the nose. -/
def allDeclared : Semantics where
  Reached := fun r b => Declared r.blocks b
  reached_declared := fun _ _ h => h

theorem allDeclared_gives_no_refutation :
    ¬ ProgramWFsem allDeclared deadBlockProgram := by
  rintro ⟨-, -, hh, -⟩
  have hb : (⟨1, [9], [], []⟩ : Block) ∈ deadBlockProgram.blocks :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hcount : deadBlockProgram.handlers.count 9 = 1 :=
    hh _ hb ⟨_, hb, rfl⟩ 9 (List.mem_cons.mpr (Or.inl rfl))
  exact absurd hcount (by decide)

/-- **The report's generality claim is false.** -/
theorem semantics_generality_claim_is_false :
    ¬ ∀ S : Semantics, ProgramWFsem S deadBlockProgram :=
  fun h => allDeclared_gives_no_refutation (h allDeclared)

/-! ## A2 — `entryOnly` is not a semantics of the block graph, and the repair

`entryOnly` declares every non-entry block unreached in EVERY program,
including one whose entry jumps straight to it. So the one fact the target's
`Semantics` assumes is too weak to make `entryOnly` a run semantics, and the
docstring's "realized by any program whose entry returns immediately" is a
claim about ONE program while `entryOnly` ranges over all of them.

The finding survives the repair, which is why this is an amendment and not a
break: at `succClosed` — reachability closed under successor edges, which every
run semantics of a block graph refines — `deadBlockProgram`'s block 1 is still
unreached and the refutation still lands. -/

def jumpProgram : RawProgram :=
  { blocks := [⟨0, [], [], [1]⟩, ⟨1, [9], [], []⟩],
    entry := 0, handlers := [9], declared := { E := [9], R := [] } }

/-- `entryOnly` calls block 1 unreached even though the entry's only exit edge
goes to it. -/
theorem entryOnly_is_not_successor_closed :
    (⟨0, [], [], [1]⟩ : Block) ∈ jumpProgram.blocks
      ∧ (1 : BlockId) ∈ (⟨0, [], [], [1]⟩ : Block).succ
      ∧ Declared jumpProgram.blocks 1
      ∧ ¬ entryOnly.Reached jumpProgram 1 := by
  refine ⟨List.mem_cons.mpr (Or.inl rfl), List.mem_cons.mpr (Or.inl rfl),
          ⟨_, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))), rfl⟩, ?_⟩
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-- Successor-closed reachability: the entry, then anything a reached declared
block points at. -/
inductive Reaches (r : RawProgram) : BlockId → Prop where
  | root : Declared r.blocks r.entry → Reaches r r.entry
  | edge {b : Block} {s : BlockId} : Reaches r b.id → b ∈ r.blocks → s ∈ b.succ →
      Declared r.blocks s → Reaches r s

theorem reaches_declared (r : RawProgram) (b : BlockId) :
    Reaches r b → Declared r.blocks b := by
  intro h; cases h with
  | root hd => exact hd
  | edge _ _ _ hd => exact hd

/-- A genuinely successor-closed instance of the target's `Semantics`. -/
def succClosed : Semantics where
  Reached := Reaches
  reached_declared := reaches_declared

/-- Under `succClosed`, `deadBlockProgram` reaches only block 0. -/
theorem deadBlock_reaches_only_entry : ∀ b, Reaches deadBlockProgram b → b = 0 := by
  intro b h
  induction h with
  | root _ => rfl
  | edge _ hb hs _ _ =>
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd hs (by simp)
    · rcases List.mem_cons.mp hb' with rfl | hb''
      · exact absurd hs (by simp)
      · exact absurd hb'' (by simp)

theorem deadBlockProgram_succClosed_wf : ProgramWFsem succClosed deadBlockProgram := by
  obtain ⟨h1, h2, -, h4⟩ := deadBlockProgram_sem_wf
  refine ⟨h1, h2, ?_, h4⟩
  intro b hb hre op hop
  have hid : b.id = 0 := deadBlock_reaches_only_entry _ hre
  rcases List.mem_cons.mp hb with rfl | hb'
  · exact absurd hop (by simp)
  · rcases List.mem_cons.mp hb' with rfl | hb''
    · exact absurd hid (by decide)
    · exact absurd hb'' (by simp)

/-- **The repaired section-7 finding.** Same conclusion, at a semantics that is
actually closed under the block graph's own edges. -/
theorem repaired_semantic_refutation :
    ProgramWFsem succClosed deadBlockProgram
      ∧ check deadBlockProgram = .error (.handlerMissing 1 9 0)
      ∧ ¬ ∃ (aer : AER) (p : CheckedProgram aer),
            check deadBlockProgram = .ok ⟨aer, p⟩ :=
  ⟨deadBlockProgram_succClosed_wf, semantic_clause_refutes_T011.2.1,
   semantic_clause_refutes_T011.2.2⟩

/-! ## A3 — the DROPPED PARENT-DELEGATION DISJUNCT

`ALGEBRA.md:304-305` spells clause 5 in full as

> `HandlersWF`: the selected direct environment has exactly one typed clause
> for every reachable operation OR A NAMED PARENT DELEGATION;

and `ALGEBRA.md:419` makes delegation first-class content ("Named parent
delegation is visible in content and checked for cycles"). The target's
`HandlersWF` drops the disjunct, and its report declares only the
reachable-to-declared change. So clause 5 is strengthened TWICE and the second
strengthening is undeclared.

Stated the way the target states its own semantic finding: parameterized, over
every delegation reading, with the single fact that op 9 of `unhandledA` is
delegated. The witness is the target's OWN `unhandledA`, whose defective block
is the ENTRY block — so this refutation is independent of reachability and is
not repaired by fixing `ALGEBRA.md:305`'s word "reachable". -/

def HandlersWFdeleg (Deleg : RawProgram → OpId → Prop) (r : RawProgram) : Prop :=
  ∀ b, b ∈ r.blocks → ∀ op, op ∈ b.ops → r.handlers.count op = 1 ∨ Deleg r op

def ProgramWFdeleg (Deleg : RawProgram → OpId → Prop) (r : RawProgram) : Prop :=
  IdsWF r ∧ EntryWF r ∧ HandlersWFdeleg Deleg r ∧ AERWF r

/-- The target's judgment is strictly stronger than clause 5's full spelling
too, so `EC1-T010` survives this defect exactly as it survives the semantic
one. This is the half that hides it. -/
theorem syn_implies_deleg (Deleg : RawProgram → OpId → Prop) {r : RawProgram}
    (h : ProgramWF r) : ProgramWFdeleg Deleg r :=
  ⟨h.1, h.2.1, fun b hb op hop => Or.inl (h.2.2.1 b hb op hop), h.2.2.2⟩

theorem unhandledA_ids : IdsWF unhandledA := by
  refine ⟨⟨fun c hc => absurd hc (by simp), trivial⟩, ?_⟩
  intro b hb s hs
  rcases List.mem_cons.mp hb with rfl | hb'
  · exact absurd hs (by simp)
  · exact absurd hb' (by simp)

/-- **Clause 5's delegation disjunct refutes `EC1-T011` a second time**, at the
entry block, for EVERY delegation reading that admits op 9 here. -/
theorem delegation_disjunct_also_refutes_T011
    (Deleg : RawProgram → OpId → Prop) (hdel : Deleg unhandledA 9) :
    ProgramWFdeleg Deleg unhandledA
      ∧ check unhandledA = .error (.handlerMissing 0 9 0)
      ∧ ¬ ∃ (aer : AER) (p : CheckedProgram aer),
            check unhandledA = .ok ⟨aer, p⟩ := by
  refine ⟨⟨unhandledA_ids, ⟨_, List.mem_cons.mpr (Or.inl rfl), rfl⟩, ?_, rfl⟩, rfl, ?_⟩
  · intro b hb op hop
    rcases List.mem_cons.mp hb with rfl | hb'
    · rcases List.mem_cons.mp hop with rfl | hop'
      · exact Or.inr hdel
      · exact absurd hop' (by simp)
    · exact absurd hb' (by simp)
  · rintro ⟨aer, p, hp⟩
    rw [show check unhandledA = .error (.handlerMissing 0 9 0) from rfl] at hp
    exact absurd hp (by simp)

/-- The defective block IS the entry, so no reachability reading excuses this
one. -/
theorem delegation_witness_is_the_entry_block :
    unhandledA.entry = 0 ∧ (⟨0, [9], [], []⟩ : Block) ∈ unhandledA.blocks
      ∧ (9 : OpId) ∈ (⟨0, [9], [], []⟩ : Block).ops :=
  ⟨rfl, List.mem_cons.mpr (Or.inl rfl), List.mem_cons.mpr (Or.inl rfl)⟩

/-! ## A4 — `EC1-F03` is NOT red at this carrier

`CONTRACT-PACKET.md:732`: "Duplicate a block/operation/handler ID." Expected
outcome: "Canonical duplicate diagnostic." Only DUPLICATE BLOCK IDS are caught
here. A duplicated operation id inside a block is normalized away by
`synthAER` before `AERWF` ever sees it, and a duplicated handler id for an
operation no block declares is never counted. The program below carries BOTH
and `check` ACCEPTS it. -/

def dupIdProgram : RawProgram :=
  { blocks := [⟨0, [9, 9], [], []⟩],
    entry := 0, handlers := [9, 7, 7], declared := { E := [9], R := [] } }

theorem dupIdProgram_wf : ProgramWF dupIdProgram :=
  clauses_sound (r := dupIdProgram) (u := ()) rfl

/-- **The duplicate-id falsifier passes through.** -/
theorem F03_duplicate_op_and_handler_ids_are_admitted :
    ProgramWF dupIdProgram
      ∧ (∃ p : CheckedProgram (synthAER dupIdProgram),
            check dupIdProgram = .ok ⟨synthAER dupIdProgram, p⟩)
      ∧ (⟨0, [9, 9], [], []⟩ : Block).ops.count 9 = 2
      ∧ dupIdProgram.handlers.count 7 = 2 :=
  ⟨dupIdProgram_wf, check_complete dupIdProgram_wf, by decide, by decide⟩

/-- And the reason it passes: normalization erases the duplication before the
only clause that could have seen it. -/
theorem synthAER_hides_the_duplicate :
    allOps dupIdProgram.blocks = [9, 9] ∧ (synthAER dupIdProgram).E = [9] :=
  ⟨rfl, rfl⟩

/-! ## A5 — `EC1-F81` stays RED

`R16` and `EC1-CE031`: first-error, never accumulating. One raw program, two
independent defects, the LATER diagnostic demanded. The later clause's finder
does condemn, and `check` refuses to return it. -/

def twoDefects : RawProgram :=
  { blocks := [⟨0, [9], [], []⟩],
    entry := 5, handlers := [], declared := { E := [9], R := [] } }

theorem F81_stays_red :
    check twoDefects = .error (.entryMissing 5)
      ∧ handlersDiag twoDefects = some (.handlerMissing 0 9 0)
      ∧ check twoDefects ≠ .error (.handlerMissing 0 9 0) := by
  refine ⟨rfl, rfl, ?_⟩
  intro hcon
  rw [show check twoDefects = Except.error (.entryMissing 5) from rfl] at hcon
  exact absurd hcon (by simp)

/-! ## A6 — `EC1-F01` and `EC1-F09` are red -/

def deletedTarget : RawProgram :=
  { blocks := [⟨0, [], [], [1]⟩], entry := 0, handlers := [],
    declared := { E := [], R := [] } }

/-- `CONTRACT-PACKET.md:730`: dangling-code diagnostic at the exact edge. -/
theorem F01_is_red : check deletedTarget = .error (.danglingSucc 0 1) := rfl

def tooSmallE : RawProgram :=
  { blocks := [⟨0, [9], [], []⟩], entry := 0, handlers := [9],
    declared := { E := [], R := [] } }

/-- `CONTRACT-PACKET.md:738`: `AERWF` mismatch carrying synthesized AND
declared rows. -/
theorem F09_is_red :
    check tooSmallE = .error (.aerMismatch ⟨[9], []⟩ ⟨[], []⟩) := rfl

/-- `CONTRACT-PACKET.md:734`, the reachable case: omitting a handler clause for
an operation of the ENTRY block is caught, naming block, operation and count. -/
theorem F05_is_red_for_the_reachable_case :
    check unhandledA = .error (.handlerMissing 0 9 0) := rfl

/-! ## A7 — the pinning the report recommends upstream makes T016 and T017 EMPTY

The report says of the bound-and-pinned alphabet: "it should be adopted
upstream rather than treated as a local convenience", because "it is what
`EC1-T017 checked_aer_exact` needs". At this carrier the opposite holds. The
`aerOk` field stores the very equation `EC1-T017` asserts, so `EC1-T017` is a
field projection with no content — the same vacuity the report correctly
diagnoses for `EC1-T010`'s `wf` field, arriving through the second field. And
`EC1-T016` is a tautology that does not even use its hypothesis. -/

/-- `EC1-T016 aer_synthesis_unique : ProgramWF r -> exists! aer, SynthAER r aer`
with `SynthAER r aer := synthAER r = aer`. Uniqueness is spelled out because
this toolchain carries no Mathlib and no `ExistsUnique` (`#check @ExistsUnique`
is an unknown identifier under `import Cas.Core.Admission`), which is itself
worth recording against the DAG's `exists!` spelling. The premise `ProgramWF r`
is DEAD: it is not mentioned, so the row has no content at this carrier. -/
theorem T016_has_no_content (r : RawProgram) :
    ∃ aer : AER, synthAER r = aer ∧ ∀ a, synthAER r = a → a = aer :=
  ⟨synthAER r, rfl, fun _ h => h.symm⟩

/-- `EC1-T017 checked_aer_exact : p : CheckedProgram aer -> SynthAER (erase p) aer`
is `CheckedProgram.aerOk`, verbatim. -/
theorem T017_is_a_field_projection {aer : AER} (p : CheckedProgram aer) :
    synthAER (erase p) = aer := p.aerOk

/-- Both together, as one statement, so the carrier-level consequence is on the
record: the index of `Sigma CheckedProgram` carries no information that
`CheckedProgram.raw` does not already determine. -/
theorem sigma_index_is_redundant (x : Sigma CheckedProgram) : synthAER x.2.raw = x.1 :=
  x.2.aerOk

/-! ## A8 — the four clauses are THREE of `ALGEBRA.md`'s twelve

`ALGEBRA.md:314-315` spells clause 10 as

> `EntryWF`: the entry accepts exactly its declared input and every normal
> return has result type `A`

— two TYPING conditions. The target's `EntryWF r := Declared r.blocks r.entry`
is reference resolution, which `ALGEBRA.md:298`'s clause 1 already owns
("every table is duplicate-free and every reference resolves"). The type layer
is absent from this carrier entirely, so neither half of clause 10 is modeled.

Checkable form of the claim: the target's `EntryWF` is exactly the resolution
predicate `IdsWF`'s second conjunct applies to successors, evaluated at the
entry. It is a clause-1 obligation wearing clause 10's name. -/

theorem entryWF_is_reference_resolution (r : RawProgram) :
    EntryWF r ↔ declaredB r.blocks r.entry = true :=
  declaredB_iff.symm

/-- Same predicate, same shape, at a successor: `IdsWF`'s second conjunct is
this very resolution property, quantified over edges. So `EntryWF` adds one
more instance of clause 1's second half; it does not model clause 10. -/
theorem ids_second_half_is_the_same_predicate (r : RawProgram) :
    (∀ b, b ∈ r.blocks → ∀ s, s ∈ b.succ → declaredB r.blocks s = true)
      ↔ (∀ b, b ∈ r.blocks → ∀ s, s ∈ b.succ → Declared r.blocks s) :=
  ⟨fun h b hb s hs => declaredB_iff.mp (h b hb s hs),
   fun h b hb s hs => declaredB_iff.mpr (h b hb s hs)⟩

/-- And `IdsWF` is literally that conjunct paired with duplicate-freedom, so
the two "clauses" the target counts separately share one obligation. -/
theorem idsWF_second_conjunct (r : RawProgram) :
    IdsWF r ↔ (NoDupIds r.blocks ∧ ∀ b, b ∈ r.blocks → ∀ s, s ∈ b.succ → Declared r.blocks s) :=
  Iff.rfl

end AttackT011

/-! ## Kernel receipts for the attacks -/

#print axioms AttackT011.allDeclared_gives_no_refutation
#print axioms AttackT011.semantics_generality_claim_is_false
#print axioms AttackT011.entryOnly_is_not_successor_closed
#print axioms AttackT011.reaches_declared
#print axioms AttackT011.deadBlock_reaches_only_entry
#print axioms AttackT011.deadBlockProgram_succClosed_wf
#print axioms AttackT011.repaired_semantic_refutation
#print axioms AttackT011.syn_implies_deleg
#print axioms AttackT011.unhandledA_ids
#print axioms AttackT011.delegation_disjunct_also_refutes_T011
#print axioms AttackT011.delegation_witness_is_the_entry_block
#print axioms AttackT011.dupIdProgram_wf
#print axioms AttackT011.F03_duplicate_op_and_handler_ids_are_admitted
#print axioms AttackT011.synthAER_hides_the_duplicate
#print axioms AttackT011.F81_stays_red
#print axioms AttackT011.F01_is_red
#print axioms AttackT011.F09_is_red
#print axioms AttackT011.F05_is_red_for_the_reachable_case
#print axioms AttackT011.T016_has_no_content
#print axioms AttackT011.T017_is_a_field_projection
#print axioms AttackT011.sigma_index_is_redundant
#print axioms AttackT011.entryWF_is_reference_resolution
#print axioms AttackT011.ids_second_half_is_the_same_predicate
#print axioms AttackT011.idsWF_second_conjunct
