import Cas.Core.Admission

/-!
# BREAKER attack file — `EC1-T012` (`workshop/s2/T012.lean`)

Adversarial re-run and falsifier battery against the landed T012 proof.
Slice `EC1-S2`. Lean `leanprover/lean4:v4.33.1`, run as

```
cd library/cas
lake env lean ../../.staging/effect-core-v1/workshop/s2/attack-EC1-T012.lean
```

Lean skill stage: `lean-assurance-review` (audit of a landed claim; read-only
against the reviewed tree — nothing in `library/`, `formal/` or any packet `.md`
is touched, and this file is the single write fence).

Sections 0-1 REPRODUCE the target's §1 abstract layer and §6 carrier VERBATIM,
because the target lives outside every lake target and cannot be imported. Every
subsequent section is an attack.

Attack index.

| § | Attack | Outcome |
|---|---|---|
| 2 | Non-vacuity: is `ProgramWF` inhabited? Is the `.ok` arm reachable? | SURVIVES — witness supplied here, NOT in the target |
| 3 | Does `decidableProgramWF` actually COMPUTE, or is it a classical ghost? | SURVIVES — kernel-reduces both ways |
| 4 | `EC1-F06` parent-delegation cycle | HITS the carrier — a 2-cycle is ADMITTED |
| 5 | `EC1-F09` alphabet claims | PARTIAL — `E` caught, `R` inexpressible, over-strict on supersets |
| 6 | `AERWF` vs `ALGEBRA.md:316` "NORMALIZES to" | BREAKS — row order decides admission |
| 7 | `ProgramWF` under block permutation | BREAKS — reordering DESTROYS well-formedness |
| 8 | `EC1-F01` deleted target block | SURVIVES — rejected, row holds |
| 9 | `EC1-F81` two defects, later diagnostic | SURVIVES — row invariant under clause reorder |
| 10 | Does the row constrain what `check` RETURNS? | BREAKS the implicit reading — it does not |
| 10b | Is the target's proposed `:221` gate sufficient? | BREAKS — the gate is blind to clause OMISSION |
| 11 | Axiom receipts | 31 receipts, no `Classical.choice` |

Two of the target's own claims were re-tested and CONFIRMED, not broken.
`∃!`/`ExistsUnique` genuinely does not elaborate in this environment
(`unexpected token '!'`; `Unknown identifier 'ExistsUnique'`), and every estate
anchor the target cites resolves at the stated line, including the two
corrections it reports against the scouts.
-/

set_option warn.classDefReducibility false

namespace AttackT012
/-! ## §0 — the target's §1, verbatim (T012.lean:89-137) -/
section Abstract

variable {R D C : Type}

/-- `EC1-T010`, abstracted: what the checker accepts is well formed. -/
def Sound (WF : R → Prop) (chk : R → Except D C) : Prop :=
  ∀ (r : R) (c : C), chk r = .ok c → WF r

/-- `EC1-T011`, abstracted: a well-formed program is accepted. The witness is
existential, which is the only closure under which the row is neither false nor
content-free. -/
def Complete (WF : R → Prop) (chk : R → Except D C) : Prop :=
  ∀ (r : R), WF r → ∃ c, chk r = .ok c

/-- `EC1-T012`, abstracted, as a named judgment so §4 can trade it against its
two parents. -/
def ErrorIff (WF : R → Prop) (chk : R → Except D C) : Prop :=
  ∀ r : R, (∃ d, chk r = .error d) ↔ ¬ WF r

/-- Forward half. Consumes `EC1-T011` ONLY: if the checker errors on `r` while
`r` were well formed, completeness would have forced an `ok`. -/
theorem not_wf_of_error {WF : R → Prop} {chk : R → Except D C}
    (hc : Complete WF chk) {r : R} (h : ∃ d, chk r = .error d) : ¬ WF r := by
  intro hwf
  obtain ⟨d, hd⟩ := h
  obtain ⟨c, hcc⟩ := hc r hwf
  rw [hd] at hcc
  exact nomatch hcc

/-- Backward half. Consumes `EC1-T010` ONLY, plus the totality of `Except`'s two
arms: an ill-formed program cannot be in the `ok` arm, and there is nowhere else
for it to be. -/
theorem error_of_not_wf {WF : R → Prop} {chk : R → Except D C}
    (hs : Sound WF chk) {r : R} (h : ¬ WF r) : ∃ d, chk r = .error d := by
  cases hx : chk r with
  | ok c => exact absurd (hs r c hx) h
  | error d => exact ⟨d, rfl⟩

/-- **`EC1-T012`.** The error branch decides exactly the complement of
`ProgramWF`.

No decidability hypothesis is used and none is available to use: `WF` is an
arbitrary `Prop`-valued predicate and no `Decidable` instance is in scope. This
is the finding against `PROOF-DAG.md:214`'s dependency column. -/
theorem check_error_iff {WF : R → Prop} {chk : R → Except D C}
    (hs : Sound WF chk) (hc : Complete WF chk) : ErrorIff WF chk :=
  fun _ => ⟨not_wf_of_error hc, error_of_not_wf hs⟩

end Abstract

/-! ## §0b — the target's `decidableOfAdequate` (T012.lean:146-167, defs only) -/
section Decidability

variable {R D C : Type}

/-- **`EC1-T012a`** — the object `EC1-T012` actually unlocks, which is a row
nowhere in the DAG. Deliberately a `def` and not an `instance`, on the estate's
own discipline: `Cas/IR/Reach.lean:550` `decidableReach` carries no `instance`
attribute because "admission is what makes reachability decidable here", and
instance resolution must never silently route a `ProgramWF` goal through a
whole-program check. -/
def decidableOfAdequate {WF : R → Prop} {chk : R → Except D C}
    (hs : Sound WF chk) (hc : Complete WF chk) : DecidablePred WF := fun r =>
  match hx : chk r with
  | .ok c    => isTrue (hs r c hx)
  | .error d => isFalse ((check_error_iff hs hc r).mp ⟨d, hx⟩)

/-- The Boolean the decision procedure computes. -/
def accepts (chk : R → Except D C) (r : R) : Bool :=
  match chk r with
  | .ok _    => true
  | .error _ => false

end Decidability

/-! ## §1 — the target's §6 carrier, verbatim (T012.lean:447-727) -/
section Carrier

abbrev BlockId := Nat
abbrev ErrTag := Nat

/-- `EC1-D005` stand-in: the alphabet triple, minus `R`. First-order. -/
structure AER where
  A : Nat
  E : List ErrTag
  deriving DecidableEq, Repr

/-- One block: an id, its successor edges, and the typed failure alternatives it
raises. `EC1-D020` says each proposed `Block` contains the existing `PProg` as
its sequential body; the body is elided here because no clause below reads it,
and no second straight-line carrier is minted. -/
structure Block where
  id     : BlockId
  succs  : List BlockId
  raises : List ErrTag
  deriving DecidableEq, Repr

/-- `EC1-D020` stand-in. -/
structure RawProgram where
  blocks      : List Block
  entry       : BlockId
  resultTy    : Nat
  declaredAER : AER
  deriving DecidableEq, Repr

/-- `EC1-D022` stand-in: a SINGLE clause-named first-error value carrying its
payload (`R16` part 1; `EC1-CE031`). Not a list, not a `NonEmpty`. -/
inductive Diagnostic where
  | duplicateBlockId (b : BlockId)
  | danglingSucc (source target : BlockId)
  | entryMissing (b : BlockId)
  | aerMismatch (synth declared : AER)
  deriving DecidableEq, Repr

/-! ### The three clauses, each a `Prop` and each with its own decision -/

/-- Clause 1, `ALGEBRA.md:296` `IdsWF`: block ids are duplicate-free and every
successor edge resolves. -/
def IdsWF (r : RawProgram) : Prop :=
  (r.blocks.map (·.id)).Nodup ∧
    ∀ b ∈ r.blocks, ∀ s ∈ b.succs, s ∈ r.blocks.map (·.id)

/-- Clause 10, `ALGEBRA.md:315` `EntryWF`, syntactic half: the entry resolves. -/
def EntryWF (r : RawProgram) : Prop := r.entry ∈ r.blocks.map (·.id)

/-- Duplicate-free tags in first-occurrence order. Applied to the SYNTHESIZED
row only — never to the raw input, which is §5's whole point. -/
def dedupTags : List ErrTag → List ErrTag
  | [] => []
  | t :: rest => if t ∈ rest then dedupTags rest else t :: dedupTags rest

/-- The raised alternatives of every block, in table order. A whole-table fold,
NOT a reachability fixpoint: see the section preamble. -/
def rawE (r : RawProgram) : List ErrTag :=
  r.blocks.foldr (fun b acc => b.raises ++ acc) []

/-- `SynthAER` as a FUNCTION, which is the only reading `ALGEBRA.md:316`'s
"synthesized A/E/R normalizes to the declared triple" supports. Recorded, not
endorsed: it is what makes `EC1-T016` a tautology, which is `T016`'s problem and
not this row's. -/
def synthAER (r : RawProgram) : AER := { A := r.resultTy, E := dedupTags (rawE r) }

/-- Clause 11, `ALGEBRA.md:316` `AERWF`. -/
def AERWF (r : RawProgram) : Prop := synthAER r = r.declaredAER

/-- `EC1-D021` stand-in, in the frozen clause order. -/
def ProgramWF (r : RawProgram) : Prop := IdsWF r ∧ EntryWF r ∧ AERWF r

/-! ### Per-clause decisions, on the RAW input -/

def dupId : List BlockId → Option BlockId
  | [] => none
  | b :: rest => if b ∈ rest then some b else dupId rest

theorem dupId_none_iff (l : List BlockId) : dupId l = none ↔ l.Nodup := by
  induction l with
  | nil => simp [dupId]
  | cons b rest ih =>
    by_cases h : b ∈ rest
    · simp [dupId, h, List.nodup_cons]
    · simp [dupId, h, ih, List.nodup_cons]

def firstDangling (ids : List BlockId) : List BlockId → Option BlockId
  | [] => none
  | s :: rest => if s ∈ ids then firstDangling ids rest else some s

theorem firstDangling_none_iff (ids ss : List BlockId) :
    firstDangling ids ss = none ↔ ∀ s ∈ ss, s ∈ ids := by
  induction ss with
  | nil => simp [firstDangling]
  | cons s rest ih =>
    by_cases h : s ∈ ids
    · simp [firstDangling, h, ih]
    · simp [firstDangling, h]

def danglingEdge (ids : List BlockId) : List Block → Option (BlockId × BlockId)
  | [] => none
  | b :: rest =>
    match firstDangling ids b.succs with
    | some s => some (b.id, s)
    | none   => danglingEdge ids rest

theorem danglingEdge_none_iff (ids : List BlockId) (bs : List Block) :
    danglingEdge ids bs = none ↔ ∀ b ∈ bs, ∀ s ∈ b.succs, s ∈ ids := by
  induction bs with
  | nil => simp [danglingEdge]
  | cons b rest ih =>
    cases hf : firstDangling ids b.succs with
    | some s =>
      simp only [danglingEdge, hf]
      constructor
      · intro h; exact nomatch h
      · intro hall
        have hn : firstDangling ids b.succs = none :=
          (firstDangling_none_iff ids b.succs).mpr (hall b List.mem_cons_self)
        rw [hf] at hn
        exact nomatch hn
    | none =>
      simp only [danglingEdge, hf]
      rw [ih]
      constructor
      · intro h b' hb' s hs
        rcases List.mem_cons.mp hb' with he | hb'
        · subst he; exact (firstDangling_none_iff ids b'.succs).mp hf s hs
        · exact h b' hb' s hs
      · intro h b' hb' s hs
        exact h b' (List.mem_cons_of_mem _ hb') s hs

def idsClause (r : RawProgram) : Option Diagnostic :=
  match dupId (r.blocks.map (·.id)) with
  | some b => some (.duplicateBlockId b)
  | none =>
    match danglingEdge (r.blocks.map (·.id)) r.blocks with
    | some p => some (.danglingSucc p.1 p.2)
    | none   => none

theorem idsClause_none_iff (r : RawProgram) : idsClause r = none ↔ IdsWF r := by
  unfold idsClause IdsWF
  cases hd : dupId (r.blocks.map (·.id)) with
  | some b =>
    simp only
    constructor
    · intro h; exact nomatch h
    · rintro ⟨hnd, -⟩
      have := (dupId_none_iff _).mpr hnd
      rw [hd] at this
      exact nomatch this
  | none =>
    cases he : danglingEdge (r.blocks.map (·.id)) r.blocks with
    | some p =>
      simp only
      constructor
      · intro h; exact nomatch h
      · rintro ⟨-, hall⟩
        have := (danglingEdge_none_iff _ _).mpr hall
        rw [he] at this
        exact nomatch this
    | none =>
      simp only
      exact ⟨fun _ => ⟨(dupId_none_iff _).mp hd, (danglingEdge_none_iff _ _).mp he⟩,
             fun _ => trivial⟩

def entryClause (r : RawProgram) : Option Diagnostic :=
  if r.entry ∈ r.blocks.map (·.id) then none else some (.entryMissing r.entry)

theorem entryClause_none_iff (r : RawProgram) : entryClause r = none ↔ EntryWF r := by
  unfold entryClause EntryWF
  by_cases h : r.entry ∈ r.blocks.map (·.id) <;> simp [h]

def aerClause (r : RawProgram) : Option Diagnostic :=
  if synthAER r = r.declaredAER then none
  else some (.aerMismatch (synthAER r) r.declaredAER)

theorem aerClause_none_iff (r : RawProgram) : aerClause r = none ↔ AERWF r := by
  unfold aerClause AERWF
  by_cases h : synthAER r = r.declaredAER <;> simp [h]

/-! ### First-error composition (`R16`) -/

/-- `R16` part 1 as a composition combinator: scan the clause decisions in the
frozen order and report the FIRST, never a set. This is the shape a twelve-clause
`ProgramWF` needs; three are instantiated below. -/
def firstError : List (Option Diagnostic) → Except Diagnostic Unit
  | [] => .ok ()
  | none :: rest => firstError rest
  | some d :: _ => .error d

/-- Soundness and completeness of the composition, in one iff, in the house
shape of `Cas/Core/Admission.lean:60` `checkRefs_ok_iff`. -/
theorem firstError_ok_iff (l : List (Option Diagnostic)) :
    firstError l = .ok () ↔ ∀ o ∈ l, o = none := by
  induction l with
  | nil => simp [firstError]
  | cons o rest ih => cases o <;> simp [firstError, ih]

theorem firstError_ok_iff3 (a b c : Option Diagnostic) :
    firstError [a, b, c] = .ok () ↔ a = none ∧ b = none ∧ c = none := by
  cases a <;> cases b <;> cases c <;> simp [firstError]

/-- The clause layer. Defined by structural recursion over the frozen clause
order and INDEPENDENTLY of `ProgramWF`; that independence is what keeps
`check_sound` from degenerating to a projection. -/
def checkClauses (r : RawProgram) : Except Diagnostic Unit :=
  firstError [idsClause r, entryClause r, aerClause r]

/-- **The real content of `EC1-T010`/`EC1-T011` at this carrier**: three
per-clause reflection lemmas composed by `firstError_ok_iff3`. -/
theorem checkClauses_ok_iff (r : RawProgram) :
    checkClauses r = .ok () ↔ ProgramWF r := by
  rw [checkClauses, firstError_ok_iff3, idsClause_none_iff, entryClause_none_iff,
    aerClause_none_iff]
  exact Iff.rfl

/-! ### `EC1-D023`/`EC1-D024` and the three rows -/

/-- `EC1-D023` stand-in. It stores evidence of `ProgramWF` (`ALGEBRA.md:320`)
and pins its own index, so `EC1-T014` and `EC1-T017` are field projections here
— which is a finding for those rows, not a defect of this one. -/
structure CheckedProgram (aer : AER) where
  raw   : RawProgram
  wf    : ProgramWF raw
  index : synthAER raw = aer

def erase {aer : AER} (p : CheckedProgram aer) : RawProgram := p.raw

/-- `EC1-D024`. The decision happens FIRST, on the raw input; the payload is
built afterwards from `checkClauses_ok_iff`, never from `decide (ProgramWF r)`.
`normalizeRaw` is not applied here — §5 is the reason. -/
def check (r : RawProgram) : Except Diagnostic (Σ aer, CheckedProgram aer) :=
  match hc : checkClauses r with
  | .error d => .error d
  | .ok ()   => .ok ⟨synthAER r, ⟨r, (checkClauses_ok_iff r).mp hc, rfl⟩⟩

theorem check_error_iff_clauses (r : RawProgram) :
    (∃ d, check r = .error d) ↔ (∃ d, checkClauses r = .error d) := by
  unfold check
  split <;> rename_i hc
  · exact ⟨fun _ => ⟨_, hc⟩, fun _ => ⟨_, rfl⟩⟩
  · simp [hc]

/-- **`EC1-T010`** at this carrier. Not a projection: the hypothesis is about
`check`, and the conclusion is reached through the three independently defined
clause decisions. -/
theorem check_sound {r : RawProgram} {x : Σ aer, CheckedProgram aer}
    (h : check r = .ok x) : ProgramWF r := by
  cases hc : checkClauses r with
  | ok u => cases u; exact (checkClauses_ok_iff r).mp hc
  | error d =>
    obtain ⟨d', hd'⟩ := (check_error_iff_clauses r).mpr ⟨d, hc⟩
    rw [h] at hd'
    exact nomatch hd'

/-- **`EC1-T011`** at this carrier, with the `Sigma` bound EXISTENTIALLY. -/
theorem check_complete {r : RawProgram} (h : ProgramWF r) :
    ∃ x : Σ aer, CheckedProgram aer, check r = .ok x := by
  have hc : checkClauses r = .ok () := (checkClauses_ok_iff r).mpr h
  refine ⟨⟨synthAER r, ⟨r, h, rfl⟩⟩, ?_⟩
  unfold check
  split <;> rename_i hc'
  · rw [hc] at hc'; exact nomatch hc'
  · rfl

theorem check_Sound : Sound ProgramWF check := fun _ _ h => check_sound h
theorem check_Complete : Complete ProgramWF check := fun _ h => check_complete h

/-- **`EC1-T012` — THE ROW**, at the carrier, in the DAG's own spelling.
Obtained by instantiating §1: the general theorem does all the work, and no
decidability hypothesis is anywhere in the derivation. -/
theorem check_error_iff' (r : RawProgram) :
    (∃ d, check r = .error d) ↔ ¬ ProgramWF r :=
  check_error_iff check_Sound check_Complete r

/-- **`EC1-T012a`** at the carrier. A `def`, not an `instance`. -/
def decidableProgramWF : DecidablePred ProgramWF :=
  decidableOfAdequate check_Sound check_Complete

end Carrier

/-! ## §2 — VACUITY PROBE: is `ProgramWF` inhabited at all?

The target proves `check_complete`, `check_error_iff'` and `decidableProgramWF`
but exhibits NO program that its checker ACCEPTS. Every example it carries
(`dupTable`, `doublyBad`) is a refutation witness. Were `ProgramWF`
unsatisfiable, `check_complete` would be vacuous and `check_error_iff'` would
collapse to "`check` always errors" — and the file would still be green.

The receipt the target omits is supplied here. The row SURVIVES: `ProgramWF` is
inhabited, and the `.ok` arm of `check` is reachable. -/

section NonVacuity

/-- One block, no edges, no raised alternatives, declared triple equal to the
synthesized one. -/
def goodProg : RawProgram :=
  { blocks := [⟨0, [], []⟩], entry := 0, resultTy := 0, declaredAER := ⟨0, []⟩ }

theorem goodProg_accepted_by_clauses : checkClauses goodProg = .ok () := rfl

/-- **`ProgramWF` is INHABITED.** The target never states this. -/
theorem goodProg_wf : ProgramWF goodProg :=
  (checkClauses_ok_iff goodProg).mp goodProg_accepted_by_clauses

/-- **The `.ok` arm of `check` is REACHABLE.** So `EC1-T011` at this carrier is
not vacuously true, and `EC1-T012`'s backward half has a non-trivial complement. -/
theorem check_ok_arm_reachable : ∃ x : Σ aer, CheckedProgram aer, check goodProg = .ok x :=
  check_complete goodProg_wf

/-- And the error arm is genuinely empty there, via the row itself. -/
theorem goodProg_no_error : ¬ (∃ d, check goodProg = .error d) :=
  fun h => (check_error_iff' goodProg).mp h goodProg_wf

/-- The target's §8 `doublyBad`, restated here (§8 lies outside the copied
carrier section): two defects — duplicate block ids and an unresolvable entry. -/
def doublyBadA : RawProgram :=
  { blocks := [⟨0, [], []⟩, ⟨0, [], []⟩], entry := 7, resultTy := 0,
    declaredAER := ⟨0, []⟩ }

theorem doublyBadA_rejected : checkClauses doublyBadA = .error (.duplicateBlockId 0) := rfl

theorem doublyBadA_not_wf : ¬ ProgramWF doublyBadA := by
  intro h
  have h2 := (checkClauses_ok_iff doublyBadA).mpr h
  rw [doublyBadA_rejected] at h2
  exact nomatch h2

end NonVacuity

/-! ## §3 — Does `decidableProgramWF` COMPUTE?

`decidability_is_never_an_obstruction` shows every `Prop` is classically
`Decidable`, so `DecidablePred ProgramWF` being INHABITED proves nothing. The
question the `PROOF-DAG.md:221` prohibition actually asks is whether the
instance the checker builds REDUCES in the kernel. Two `rfl` receipts settle it:
both arms of `decidableOfAdequate` evaluate. The row SURVIVES this attack. -/

section Computes

theorem decidableProgramWF_reduces_true :
    @decide (ProgramWF goodProg) (decidableProgramWF goodProg) = true := rfl

theorem decidableProgramWF_reduces_false :
    @decide (ProgramWF doublyBadA) (decidableProgramWF doublyBadA) = false := rfl

end Computes

/-! ## §4 — `EC1-F06`: add a parent-delegation cycle

The battery's `EC1-F06` demands the checker reject a delegation cycle
(`ALGEBRA.md:299` clause 4, "region nesting is acyclic"). The carrier HAS the
edge relation — `Block.succs`, and `IdsWF` already quantifies over it — but no
acyclicity clause. So the falsifier HITS: a two-block cycle is ADMITTED, and
`EC1-T012` reports it as well formed.

This is not a defect in the row; it is the exact size of the carrier's green
check, and it is not stated in the target's omissions list, which names the nine
missing clauses without exhibiting a program any of them would have caught. -/

section F06

def cyclicProg : RawProgram :=
  { blocks := [⟨0, [1], []⟩, ⟨1, [0], []⟩], entry := 0, resultTy := 0,
    declaredAER := ⟨0, []⟩ }

theorem cyclicProg_accepted : checkClauses cyclicProg = .ok () := rfl

/-- **`EC1-F06` is RED against this carrier**: the cycle `0 → 1 → 0` is well
formed. -/
theorem cyclicProg_wf : ProgramWF cyclicProg :=
  (checkClauses_ok_iff cyclicProg).mp cyclicProg_accepted

theorem cyclicProg_admitted : ∃ x : Σ aer, CheckedProgram aer, check cyclicProg = .ok x :=
  check_complete cyclicProg_wf

/-- The cycle is really there: block `0` names `1` and block `1` names `0`. -/
theorem cyclicProg_has_a_cycle :
    (∃ b ∈ cyclicProg.blocks, b.id = 0 ∧ 1 ∈ b.succs) ∧
    (∃ b ∈ cyclicProg.blocks, b.id = 1 ∧ 0 ∈ b.succs) := by
  constructor
  · exact ⟨⟨0, [1], []⟩, by decide, rfl, by decide⟩
  · exact ⟨⟨1, [0], []⟩, by decide, rfl, by decide⟩

end F06

/-! ## §5 — `EC1-F09`: claim too-small `E` or `R`

Half the falsifier lands, half is INEXPRESSIBLE.

* too-small `E` is caught (`pSmallE`);
* too-LARGE `E` is also rejected (`pBigE`) — `AERWF` is equality, so the
  target's own description of `synthAER` as "a MAY over-approximation" does not
  hold of the CLAUSE: a program declaring more alternatives than it can raise is
  condemned, not admitted;
* `R` cannot be claimed at all, small or large. The carrier's `AER` has exactly
  two fields, receipted below, so the requirement row has no representation and
  `EC1-F09`'s `R` half cannot be run here. -/

section F09

/-- The carrier's alphabet is exactly `A` and `E`. No `R` row exists to under-
or over-claim, so half of `EC1-F09` has nothing to bite. -/
theorem AER_has_no_R_row : ∀ a : AER, a = ⟨a.A, a.E⟩ := fun _ => rfl

/-- Raises tag `1`, declares no alternatives. -/
def pSmallE : RawProgram :=
  { blocks := [⟨0, [], [1]⟩], entry := 0, resultTy := 0, declaredAER := ⟨0, []⟩ }

theorem pSmallE_rejected : checkClauses pSmallE = .error (.aerMismatch ⟨0, [1]⟩ ⟨0, []⟩) := rfl

theorem pSmallE_not_wf : ¬ ProgramWF pSmallE := by
  intro h
  have h2 := (checkClauses_ok_iff pSmallE).mpr h
  rw [pSmallE_rejected] at h2
  exact nomatch h2

/-- Raises tag `1`, declares `[1,2]` — a strict SUPERSET of what it can raise. -/
def pBigE : RawProgram :=
  { blocks := [⟨0, [], [1]⟩], entry := 0, resultTy := 0, declaredAER := ⟨0, [1, 2]⟩ }

theorem pBigE_rejected : checkClauses pBigE = .error (.aerMismatch ⟨0, [1]⟩ ⟨0, [1, 2]⟩) := rfl

/-- **The clause is not a MAY over-approximation.** Declaring a superset is
condemned. -/
theorem pBigE_not_wf : ¬ ProgramWF pBigE := by
  intro h
  have h2 := (checkClauses_ok_iff pBigE).mpr h
  rw [pBigE_rejected] at h2
  exact nomatch h2

end F09

/-! ## §6 — `AERWF` vs `ALGEBRA.md:316`: "NORMALIZES to", read as raw equality

Clause 11 reads "synthesized `A/E/R` **normalizes to** the declared triple", and
clause 3 (`ALGEBRA.md:296` `RowsWF`) reads "all rows are **canonical**". The
target implements clause 11 as `synthAER r = r.declaredAER` — raw list equality,
with `dedupTags` preserving TABLE ORDER and normalizing nothing.

Consequence: admission is decided by the ORDER of the declared row. Two programs
declaring the same alternatives, differing only in the spelling of the list, are
partitioned by `EC1-T012` — one admitted, one condemned. The target records
`synthAER`-as-a-function as its divergence; the ORDER SENSITIVITY of the
comparison is not recorded anywhere and is a separate defect.

This is also where the carrier diverges from its own siblings. `T011.lean:149`
`normRow`, `T013.lean:260` `canon` and `T016.lean:174` `canon` are all ordered
inserts producing an ASCENDING row; `T016.lean:296` puts `canon` on the DECLARED
side and `T017.lean:744` puts `normalizeAER` there. `T012.lean`'s `dedupTags` is
the only one of the five that sorts nothing. -/

section RowOrder

/-- Two blocks raising `1` and `2`, declaring `[1,2]`. Admitted. -/
def pDecl12 : RawProgram :=
  { blocks := [⟨0, [], [1]⟩, ⟨1, [], [2]⟩], entry := 0, resultTy := 0,
    declaredAER := ⟨0, [1, 2]⟩ }

/-- The SAME program declaring the SAME alternatives, spelled `[2,1]`. -/
def pDecl21 : RawProgram :=
  { blocks := [⟨0, [], [1]⟩, ⟨1, [], [2]⟩], entry := 0, resultTy := 0,
    declaredAER := ⟨0, [2, 1]⟩ }

/-- The two declared rows have exactly the same members. -/
theorem decl_rows_have_equal_members :
    ∀ t : ErrTag, t ∈ pDecl12.declaredAER.E ↔ t ∈ pDecl21.declaredAER.E := by
  intro t
  constructor <;> · intro h; simp only [pDecl12, pDecl21, List.mem_cons,
    List.not_mem_nil, or_false] at h ⊢; exact h.symm

theorem pDecl12_wf : ProgramWF pDecl12 := (checkClauses_ok_iff pDecl12).mp rfl

theorem pDecl21_rejected :
    checkClauses pDecl21 = .error (.aerMismatch ⟨0, [1, 2]⟩ ⟨0, [2, 1]⟩) := rfl

theorem pDecl21_not_wf : ¬ ProgramWF pDecl21 := by
  intro h
  have h2 := (checkClauses_ok_iff pDecl21).mpr h
  rw [pDecl21_rejected] at h2
  exact nomatch h2

/-- **The break.** `EC1-T012` partitions two programs whose declared alphabets
have identical members. Admission is decided by list spelling, not by the row. -/
theorem row_spelling_decides_admission :
    (¬ ∃ d, check pDecl12 = .error d) ∧ (∃ d, check pDecl21 = .error d) :=
  ⟨fun h => (check_error_iff' pDecl12).mp h pDecl12_wf,
   (check_error_iff' pDecl21).mpr pDecl21_not_wf⟩

end RowOrder

/-! ## §7 — `ProgramWF` is NOT invariant under block permutation

`synthAER` folds the block table in TABLE ORDER, so permuting the block list
permutes the synthesized row. Well-formedness therefore depends on the order of
a table that `IdsWF` already forces to be a duplicate-free SET of ids.

This is the second half of the target's §5 obligation, and it points the other
way. §5 proves that a normalizer running BEFORE the decision can CREATE
well-formedness (`T012_fails_for_normalize_then_check`). §7 proves that at the
target's OWN carrier a reordering normalizer DESTROYS it. `Cas/Backend/Canon.lean`'s
`canonServices` — the very normalizer §5 uses — is a `mergeSort`, so it reorders.
So the transfer lemma the target lists as owed
(`programWF_normalizeRaw : ProgramWF (normalizeRaw r) ↔ ProgramWF r`) is FALSE in
BOTH directions at this carrier, not just forwards.

The target's §5 reports only the creation half. -/

section BlockOrder

/-- The blocks of `pDecl12`, swapped. Same block set, same declared row. -/
def pSwapped : RawProgram :=
  { blocks := [⟨1, [], [2]⟩, ⟨0, [], [1]⟩], entry := 0, resultTy := 0,
    declaredAER := ⟨0, [1, 2]⟩ }

theorem swapped_same_block_set :
    ∀ b : Block, b ∈ pDecl12.blocks ↔ b ∈ pSwapped.blocks := by
  intro b
  simp [pDecl12, pSwapped]
  constructor <;> rintro (h | h) <;> simp [h]

theorem pSwapped_rejected :
    checkClauses pSwapped = .error (.aerMismatch ⟨0, [2, 1]⟩ ⟨0, [1, 2]⟩) := rfl

/-- **The break.** Reordering the block table turns a well-formed program into
an ill-formed one. -/
theorem block_order_decides_admission : ProgramWF pDecl12 ∧ ¬ ProgramWF pSwapped := by
  refine ⟨pDecl12_wf, ?_⟩
  intro h
  have h2 := (checkClauses_ok_iff pSwapped).mpr h
  rw [pSwapped_rejected] at h2
  exact nomatch h2

/-- Stated as the failure of the owed transfer lemma's DESTRUCTION direction:
no `norm` that merely reorders blocks can satisfy
`ProgramWF r → ProgramWF (norm r)`. -/
theorem no_reordering_normalizer_preserves_wf :
    ¬ ∀ norm : RawProgram → RawProgram,
        (∀ r, ∀ b : Block, b ∈ (norm r).blocks ↔ b ∈ r.blocks) →
        (∀ r, ProgramWF r → ProgramWF (norm r)) := by
  intro hall
  have := hall (fun r => if r = pDecl12 then pSwapped else r)
    (by
      intro r b
      by_cases hr : r = pDecl12
      · subst hr; exact (swapped_same_block_set b).symm
      · simp only [if_neg hr])
    pDecl12 pDecl12_wf
  exact block_order_decides_admission.2 this

/-- And the synthesized row is not canonical in the siblings' sense: `T016.lean`'s
`RowsWF` is `Ascending`, and this row is not. So a `ProgramWF` accepted here can
fail `ALGEBRA.md:296` clause 3 as `T016.lean:295` states it. -/
theorem synth_row_not_ascending : ¬ List.Pairwise (· < ·) (synthAER pSwapped).E := by
  decide

end BlockOrder

/-! ## §8 — `EC1-F01`: delete the target block

Removing a block that a live edge names must condemn the program. The falsifier
SURVIVES: `IdsWF`'s resolution half catches it and `EC1-T012` reports the
error arm. -/

section F01

/-- `0 → 1`, with block `1` deleted from the table. -/
def pDeleted : RawProgram :=
  { blocks := [⟨0, [1], []⟩], entry := 0, resultTy := 0, declaredAER := ⟨0, []⟩ }

theorem pDeleted_rejected : checkClauses pDeleted = .error (.danglingSucc 0 1) := rfl

theorem pDeleted_not_wf : ¬ ProgramWF pDeleted := by
  intro h
  have h2 := (checkClauses_ok_iff pDeleted).mpr h
  rw [pDeleted_rejected] at h2
  exact nomatch h2

theorem pDeleted_row : ∃ d, check pDeleted = .error d :=
  (check_error_iff' pDeleted).mpr pDeleted_not_wf

end F01

/-! ## §9 — `EC1-F81`: two independent defects, demand the LATER diagnostic

The falsifier that killed `EC1-T015`'s previous form. Against `EC1-T012` it is
STRUCTURALLY BLIND, and the demonstration below is stronger than the target's
§8, which shows only that two `Bool → Except Nat Unit` toys agree.

A SECOND checker is built at the target's own carrier by permuting the frozen
clause order. It satisfies `EC1-T010`, `EC1-T011` and `EC1-T012` for the SAME
`ProgramWF`, and on `doublyBadA` it reports the OTHER condemning clause. So the
row cannot see which of the two defects is reported, in either direction, and
`EC1-F81` stays red against `EC1-T015` without touching `EC1-T012`. -/

section F81

/-- The clause order reversed. Nothing else changes. -/
def checkClauses' (r : RawProgram) : Except Diagnostic Unit :=
  firstError [aerClause r, entryClause r, idsClause r]

theorem checkClauses'_ok_iff (r : RawProgram) : checkClauses' r = .ok () ↔ ProgramWF r := by
  rw [checkClauses', firstError_ok_iff3, aerClause_none_iff, entryClause_none_iff,
    idsClause_none_iff]
  constructor
  · rintro ⟨ha, he, hi⟩; exact ⟨hi, he, ha⟩
  · rintro ⟨hi, he, ha⟩; exact ⟨ha, he, hi⟩

theorem check'_Sound : Sound ProgramWF checkClauses' := by
  intro r u h; cases u; exact (checkClauses'_ok_iff r).mp h

theorem check'_Complete : Complete ProgramWF checkClauses' :=
  fun r h => ⟨(), (checkClauses'_ok_iff r).mpr h⟩

/-- The permuted checker satisfies the row too. -/
theorem check'_error_iff : ErrorIff ProgramWF checkClauses' :=
  check_error_iff check'_Sound check'_Complete

/-- The frozen order reports the id clause. -/
theorem doublyBadA_first_order : checkClauses doublyBadA = .error (.duplicateBlockId 0) := rfl

/-- The permuted order reports the entry clause — the LATER defect under the
target's own frozen order. -/
theorem doublyBadA_second_order : checkClauses' doublyBadA = .error (.entryMissing 7) := rfl

/-- **`EC1-T012` cannot separate them.** Two checkers, both satisfying the row
for the same predicate, reporting different condemning clauses on the same
input. Whatever `EC1-F81` decides about `EC1-T015`, `EC1-T012` is unaffected —
and equally, `EC1-T012` licenses NOTHING about diagnostics. -/
theorem F81_is_blind_to_T012 :
    ErrorIff ProgramWF checkClauses ∧ ErrorIff ProgramWF checkClauses' ∧
      checkClauses doublyBadA ≠ checkClauses' doublyBadA := by
  refine ⟨?_, check'_error_iff, ?_⟩
  · exact check_error_iff
      (by intro r u h; cases u; exact (checkClauses_ok_iff r).mp h)
      (fun r h => ⟨(), (checkClauses_ok_iff r).mpr h⟩)
  · rw [doublyBadA_first_order, doublyBadA_second_order]
    intro h; exact nomatch h

end F81

/-! ## §10 — The row pins the PARTITION and NOT the payload

The target's §8 records that `EC1-T012` "does not determine the diagnostic". The
stronger and unreported scope limit is on the other arm: `EC1-T010`, `EC1-T011`
and `EC1-T012`, as stated, say NOTHING about the `CheckedProgram` the checker
returns. `Sound` reads `chk r = .ok c → WF r` and `Complete` reads
`WF r → ∃ c, chk r = .ok c`; in neither is `c` related to `r`.

`bogusCheck` below decides exactly like the target's `check` and then returns a
FIXED, unrelated checked program on every accept. It satisfies all three rows.
So `EC1-K10`, `EC1-T013` and `EC1-T014` carry the whole of the payload
obligation, and no reading of `EC1-T012` may be used to support any claim about
what admission produces. -/

section Payload

def bogusCheck (r : RawProgram) : Except Diagnostic (Σ aer, CheckedProgram aer) :=
  match checkClauses r with
  | .error d => .error d
  | .ok ()   => .ok ⟨synthAER goodProg, ⟨goodProg, goodProg_wf, rfl⟩⟩

theorem bogus_Sound : Sound ProgramWF bogusCheck := by
  intro r c h
  cases hcl : checkClauses r with
  | ok u => cases u; exact (checkClauses_ok_iff r).mp hcl
  | error d => exfalso; unfold bogusCheck at h; rw [hcl] at h; exact nomatch h

theorem bogus_Complete : Complete ProgramWF bogusCheck := by
  intro r h
  have hc : checkClauses r = .ok () := (checkClauses_ok_iff r).mpr h
  refine ⟨⟨synthAER goodProg, ⟨goodProg, goodProg_wf, rfl⟩⟩, ?_⟩
  unfold bogusCheck; rw [hc]

/-- `bogusCheck` satisfies `EC1-T012` verbatim. -/
theorem bogus_error_iff : ErrorIff ProgramWF bogusCheck :=
  check_error_iff bogus_Sound bogus_Complete

/-- **The break in the implicit reading.** An adequate checker may return a
checked program that is not the input at all. -/
theorem row_does_not_pin_the_payload :
    ∃ (r : RawProgram) (x : Σ aer, CheckedProgram aer),
      bogusCheck r = .ok x ∧ x.2.raw ≠ r := by
  refine ⟨pDecl12, ⟨synthAER goodProg, ⟨goodProg, goodProg_wf, rfl⟩⟩, ?_, by decide⟩
  unfold bogusCheck
  rw [show checkClauses pDecl12 = .ok () from rfl]

end Payload

/-! ## §10b — The `PROOF-DAG.md:221` gate the target proposes is not sufficient

The target's result D proposes a dispatch-brief gate: "`check` must be a
computable `def`, never `noncomputable`, and `#print axioms check_complete` must
not show `Classical.choice`. Nothing else will catch a silently-semantic clause."

That gate is blind to the failure mode actually present. `PROOF-DAG.md:221`
prohibits `EC1-T011`/`EC1-T012` when a `ProgramWF` clause is silently changed;
the carrier under review silently DROPS nine of the twelve `ALGEBRA.md` §4.3
clauses, including clause 4's acyclicity, and §4 above exhibits a program the
dropped clause condemns and this checker admits. Yet `check` is a computable
`def` and `check_complete`'s receipt in the target reads `[propext, Quot.sound]`
— the proposed gate is GREEN throughout.

An axiom receipt detects classical reasoning in a PROOF. It cannot detect a
predicate that was weakened before the proof began. The gate that would catch
this is a clause-coverage obligation — twelve named clauses, each with its own
reflection lemma — not an axiom line.

`cyclicProg_wf` and `cyclicProg_admitted` above are that demonstration; no new
theorem is needed here. -/

/-! ## §11 — Axiom receipts

No `sorry`, no `axiom`, no `native_decide`, no `#eval` standing for a claim.
`Classical.choice` appears nowhere below: every attack in this file is
axiom-free or rests only on `propext`/`Quot.sound`. -/

section Receipts

#print axioms goodProg_wf
#print axioms check_ok_arm_reachable
#print axioms goodProg_no_error
#print axioms doublyBadA_not_wf
#print axioms decidableProgramWF_reduces_true
#print axioms decidableProgramWF_reduces_false
#print axioms cyclicProg_wf
#print axioms cyclicProg_admitted
#print axioms cyclicProg_has_a_cycle
#print axioms AER_has_no_R_row
#print axioms pSmallE_not_wf
#print axioms pBigE_not_wf
#print axioms decl_rows_have_equal_members
#print axioms pDecl12_wf
#print axioms pDecl21_not_wf
#print axioms row_spelling_decides_admission
#print axioms swapped_same_block_set
#print axioms block_order_decides_admission
#print axioms no_reordering_normalizer_preserves_wf
#print axioms synth_row_not_ascending
#print axioms pDeleted_not_wf
#print axioms pDeleted_row
#print axioms checkClauses'_ok_iff
#print axioms check'_error_iff
#print axioms doublyBadA_first_order
#print axioms doublyBadA_second_order
#print axioms F81_is_blind_to_T012
#print axioms bogus_Sound
#print axioms bogus_Complete
#print axioms bogus_error_iff
#print axioms row_does_not_pin_the_payload

end Receipts

end AttackT012
