import Cas.Core.Admission
import Cas.Lang.Defun

/-!
# Effect Core v1 — `EC1-T013` (`check_erase`), slice `EC1-S2`

Workshop artifact only. Nothing here is proposed for `library/` or for
`formal/effect-core-v1/EffectCore/Admission/Check.lean`.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/T013.lean
```

The DAG row under implementation is

```text
EC1-T013  check_erase : check (erase p) = ok <a, normalizeChecked p>   deps T006, T010
```

Lean skill stage: `lean-algebraic-systems` (operations, checker, interpreter
boundary). Its entry condition — "a contract naming operations, observables,
invalid scenarios, and environment assumptions" — does NOT hold: `RawProgram`
(`EC1-D020`), `ProgramWF` (`D021`), `Diagnostic` (`D022`), `CheckedProgram`
(`D023`), `check` (`D024`), `erase` (`D025`), `normalizeRaw` (`D026`) are all
`PROPOSED TERM` prose rows and `normalizeChecked` is not even that. The stage's
own instruction in that case is to perform a pre-model pass and carry the
missing choices as explicit alternatives. That is what §2 does: it builds the
MINIMUM carrier this one theorem needs, names every choice it makes, and proves
the row there. §1 is carrier-free and transfers to whatever the sibling agents
built.

## Findings

| § | Question | Finding |
|---|---|---|
| 1.1 | Is the row vacuous? | YES, for any `normalizeChecked` read off `check`. |
| 1.2 | What does the row force? | `normalizeChecked` FACTORS THROUGH `erase`. |
| 1.3 | What does `EC1-K10` add? | It forces `erase (normalizeChecked p) = erase p`. |
| 1.4 | With `CheckedProgram.ext`? | `normalizeChecked = id`. The row's function is a phantom. |
| 1.5 | And then? | The row FORCES `erase` injective at each index. |
| 1.6 | Does the row entail `EC1-T017`? | YES, on the nose, from the Sigma index. |
| 2 | Is the row provable at a real checker? | YES — `check_erase`, §2.9, at a 4-clause `ProgramWF`. |
| 2.10 | Is the row satisfiable at a lossy carrier? | NO. `no_checker_satisfies_check_erase_on_CheckedPlus`. |
| 2.11 | May `check` normalize before it decides? | NO. `programWF_normalizeRaw_is_not_reversible`. |
| 2.12 | Is `EC1-T014` a theorem? | NO, a field projection. The DAG's `T013 <-> T014` cycle dissolves. |

## Assumptions

`EC1-T006` (`normalizeRaw_idempotent`) belongs to slice `EC1-S1`, running
concurrently; I did not read `workshop/s1/`. It is used in §1 ONLY as a named
hypothesis. §2 proves the ANALOGUE for its own row normalizer (`canon_idem`);
that is a fact about this file's `canon`, and it does NOT discharge `EC1-T006`
for `EC1-D026`.

Every clause name below is a NAMED SUBSET of `ALGEBRA.md` §4.3's twelve. This
file implements clauses 1 (`IdsWF`), 2-fragment (`BodiesWF`), 10 (`EntryWF`)
and 11 (`AERWF`). Clauses 3-9 and 12 are NOT modelled. The row is therefore
proved at a weaker `ProgramWF` than the packet's.

## Reuse

`RawBlock.body : Cas.Lang.PProg` — the estate's straight-line carrier, as
`PROOF-DAG.md`:121-123 requires ("Each proposed `Block` contains the existing
`PProg` as its sequential body"). No second line/table type is minted, and
`BodiesWF` is stated with the estate's own `Cas.Lang.PLine.WF`.

## The DAG's dependency column, corrected

`PROOF-DAG.md`:215 rows this theorem `deps T006, T010`.

* `T006` is CORRECT, and §2.9 shows why the DAG could not have known it from the
  signature: the row needs idempotence not through `normalizeChecked` but
  through `check` ITSELF. Under `EC1-K10` the `canonical` field of every value
  `check` builds is `normalizeRaw (normalizeRaw r) = normalizeRaw r`. No checked
  program can be constructed at all without it.
* `T010` is WRONG. `check_sound` points the wrong way: it cannot establish that
  `check (erase p)` SUCCEEDS. The success premise is `ProgramWF (erase p)`,
  which is `EC1-T014` — and the DAG routes `T014` through `T013`. §1.7 and
  §2.12 break that cycle: `T014` is a field selector, so `check_erase` consumes
  `p.wf` directly and `EC1-T010` is not in its proof route at all. The honest
  column is `T006, T011, T014-as-projection, erase_check, CheckedProgram.ext`.
-/

namespace EffectCoreT013

open Cas.Lang (PIn PLine PProg)

/-! ## §1 — carrier-free results

Everything in this section is proved of an ARBITRARY `Raw`, `Diag`, index type
`Idx` and family `Chk : Idx -> Type`. It therefore applies to whatever carrier
each sibling S2 agent built, and it is what the coordinator should diff the
eight files against. `erase` and `normalizeChecked` are taken with an EXPLICIT
index argument so that no implicit-binder convention is smuggled in. -/

section CarrierFree

variable {Raw Diag Idx : Type} {Chk : Idx → Type}

/-! ### §1.1 — the row is a tautology under a checker-derived normalizer

`normalizeChecked` is named at `PROOF-DAG.md`:215 and `CONTRACT-PACKET.md`:310
and DECLARED NOWHERE: it is absent from the `EC1-D020`–`D026` term list, which
declares `normalizeRaw` (`D026`) and nothing else. Nothing therefore forbids
reading it off the checker, and under that reading the row proves nothing
beyond admission of erasures. -/

/-- Read the checked normalizer off the checker. -/
def lazyNormalizeChecked (check : Raw → Except Diag (Σ a, Chk a))
    (erase : ∀ a, Chk a → Raw) (a : Idx) (p : Chk a) : Σ b, Chk b :=
  match check (erase a p) with
  | .ok q => q
  | .error _ => ⟨a, p⟩

/-- VACUITY. For EVERY `check` and EVERY `erase`, once erasures are assumed to
admit, `EC1-T013` holds by computation. All of the row's content sits in the
hypothesis `hadm` — that is, in `EC1-T014` plus `EC1-T011`, and the DAG routes
`EC1-T014` THROUGH this row. -/
theorem check_erase_is_vacuous_under_a_checker_derived_normalizer
    (check : Raw → Except Diag (Σ a, Chk a)) (erase : ∀ a, Chk a → Raw)
    (hadm : ∀ (a : Idx) (p : Chk a), ∃ q, check (erase a p) = .ok q) :
    ∀ (a : Idx) (p : Chk a),
      check (erase a p) = .ok (lazyNormalizeChecked check erase a p) := by
  intro a p
  obtain ⟨q, hq⟩ := hadm a p
  have hn : lazyNormalizeChecked check erase a p = q := by
    show (match check (erase a p) with | .ok q => q | .error _ => ⟨a, p⟩) = q
    rw [hq]
  rw [hn, hq]

/-! ### §1.2 — the row forces `normalizeChecked` to factor through `erase` -/

/-- A `Sigma` equality at a FIXED index is a component equality. Used below and
in §2; the schematic DAG signature hides this step. -/
theorem sigma_same_index {a : Idx} {x y : Chk a}
    (h : (⟨a, x⟩ : Σ b, Chk b) = ⟨a, y⟩) : x = y :=
  eq_of_heq (Sigma.mk.inj h).2

/-- CARRIER CONSTRAINT. Two checked programs with the same erasure have the
same normal form. Consequence: `CheckedProgram` may carry no data that `erase`
discards and `check` cannot recompute. This is the `hsep` analogue of
`Cas/Lang/Defun.lean:998 decodeProg_encodeProg` — but where the estate's round
trip pays with a PREMISE whose necessity it exhibits at `Defun.lean:1023`,
`EC1-T013` pays by silently constraining the carrier. -/
theorem normalizeChecked_factors_through_erase
    (check : Raw → Except Diag (Σ a, Chk a)) (erase : ∀ a, Chk a → Raw)
    (normalizeChecked : ∀ a, Chk a → Chk a)
    (T013 : ∀ (a : Idx) (p : Chk a),
      check (erase a p) = .ok ⟨a, normalizeChecked a p⟩)
    {a : Idx} (p q : Chk a) (h : erase a p = erase a q) :
    normalizeChecked a p = normalizeChecked a q := by
  have hp := T013 a p
  rw [h, T013 a q] at hp
  exact (sigma_same_index (Except.ok.inj hp)).symm

/-! ### §1.3 — what `EC1-K10` adds

`CONTRACT-PACKET.md`:309 (`EC1-K10`) requires `erase checked = normalizeRaw
(erase checked)`. Together with the unlisted companion `erase_check` — "a
successful check erases back to the normalized raw it was given", which the DAG
does not row — the pair pins the erasure of the normal form. NO carrier
extensionality is used here. -/

theorem normalizeChecked_preserves_erasure
    {normalizeRaw : Raw → Raw}
    (check : Raw → Except Diag (Σ a, Chk a)) (erase : ∀ a, Chk a → Raw)
    (normalizeChecked : ∀ a, Chk a → Chk a)
    (T013 : ∀ (a : Idx) (p : Chk a),
      check (erase a p) = .ok ⟨a, normalizeChecked a p⟩)
    (erase_check : ∀ (r : Raw) (a : Idx) (q : Chk a),
      check r = .ok ⟨a, q⟩ → erase a q = normalizeRaw r)
    (K10 : ∀ (a : Idx) (p : Chk a), normalizeRaw (erase a p) = erase a p)
    (a : Idx) (p : Chk a) : erase a (normalizeChecked a p) = erase a p := by
  rw [erase_check _ _ _ (T013 a p), K10]

/-! ### §1.4 — with carrier extensionality the normalizer is the identity -/

/-- `EC1-T013` + `erase_check` + `EC1-K10` + extensionality ⟹ `normalizeChecked`
is `id`. So under the packet's OWN contract clause the row's normalizer names
no function: the honest spelling of the row is `check (erase p) = ok <a, p>`
and `normalizeChecked` should be deleted from `PROOF-DAG.md`:215 and
`CONTRACT-PACKET.md`:310. -/
theorem normalizeChecked_is_forced_to_be_the_identity
    {normalizeRaw : Raw → Raw}
    (check : Raw → Except Diag (Σ a, Chk a)) (erase : ∀ a, Chk a → Raw)
    (normalizeChecked : ∀ a, Chk a → Chk a)
    (ext : ∀ (a : Idx) (x y : Chk a), erase a x = erase a y → x = y)
    (T013 : ∀ (a : Idx) (p : Chk a),
      check (erase a p) = .ok ⟨a, normalizeChecked a p⟩)
    (erase_check : ∀ (r : Raw) (a : Idx) (q : Chk a),
      check r = .ok ⟨a, q⟩ → erase a q = normalizeRaw r)
    (K10 : ∀ (a : Idx) (p : Chk a), normalizeRaw (erase a p) = erase a p)
    (a : Idx) (p : Chk a) : normalizeChecked a p = p :=
  ext _ _ _ (normalizeChecked_preserves_erasure (normalizeRaw := normalizeRaw)
    check erase normalizeChecked T013 erase_check K10 a p)

/-! ### §1.5 — the identity form forces `erase` injective at each index

This is the converse pressure, and it is what makes §2.10 a refutation rather
than an inconvenience: extensionality is not an optional convenience lemma, the
row DEMANDS it. -/

theorem check_erase_id_forces_erase_injective
    (check : Raw → Except Diag (Σ a, Chk a)) (erase : ∀ a, Chk a → Raw)
    (T013id : ∀ (a : Idx) (p : Chk a), check (erase a p) = .ok ⟨a, p⟩)
    {a : Idx} (p q : Chk a) (h : erase a p = erase a q) : p = q := by
  have hp := T013id a p
  rw [h, T013id a q] at hp
  exact (sigma_same_index (Except.ok.inj hp)).symm

/-! ### §1.6 — the row entails `EC1-T017`

For the DAG's right-hand side `ok <a, normalizeChecked p>` to typecheck, `a`
must be `p`'s OWN index. So the row asserts index exactness on the nose, which
is `EC1-T017 checked_aer_exact`. The DAG routes `T017` through `T016` and does
not record the entailment. -/

theorem check_erase_entails_index_exactness
    (check : Raw → Except Diag (Σ a, Chk a)) (erase : ∀ a, Chk a → Raw)
    (normalizeChecked : ∀ a, Chk a → Chk a)
    (T013 : ∀ (a : Idx) (p : Chk a),
      check (erase a p) = .ok ⟨a, normalizeChecked a p⟩)
    {a : Idx} (p : Chk a) {a' : Idx} {q : Chk a'}
    (h : check (erase a p) = .ok ⟨a', q⟩) : a' = a := by
  rw [T013 a p] at h
  exact (congrArg Sigma.fst (Except.ok.inj h)).symm

/-! ### §1.7 — `EC1-T014` is not a theorem, and the DAG's cycle dissolves

`PROOF-DAG.md`:216 rows `T014 erase_wf : ProgramWF (erase p)` with `deps
T010,T013`, while `T013`'s success premise is exactly `ProgramWF (erase p)`.
`ALGEBRA.md`:319-320 and `REIFICATION-CHECKLIST.md`:859 both say
`CheckedProgram` STORES the evidence, so `erase_wf` is a field selector — with
no checker in scope at all. §2.12 is the concrete instance. -/

theorem erase_wf_is_a_projection {Raw : Type} {WF : Raw → Prop}
    (p : { r : Raw // WF r }) : WF p.val := p.property

end CarrierFree

/-! ## §2 — a concrete admission boundary, and the row proved in it

Minimum carrier this one theorem needs. Every choice is named. -/

/-! ### §2.1 — canonical rows

The row alphabet is `Nat` keys. `canon` is insertion sort with dedup, written
by hand: `Cas/Backend/Canon.lean`'s `List.mergeSort` family is the estate's own
normalizer but it carries `Classical.choice` (the ceiling `EC1-CE030` records),
and this file reports no classical axiom anywhere. -/

/-- Insert into a strictly increasing list, dropping duplicates. -/
def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if y < x then y :: ins x ys else y :: ys

/-- The canonical spelling of a row. -/
def canon : List Nat → List Nat
  | [] => []
  | x :: xs => ins x (canon xs)

/-- Strictly increasing, head-against-tail. -/
def SortedLt : List Nat → Prop
  | [] => True
  | x :: xs => (∀ y ∈ xs, x < y) ∧ SortedLt xs

theorem mem_ins {x y : Nat} : ∀ {l : List Nat}, y ∈ ins x l ↔ y = x ∨ y ∈ l
  | [] => by simp [ins]
  | z :: zs => by
      by_cases h1 : x < z
      · simp [ins, h1]
      · by_cases h2 : z < x
        · simp only [ins, if_neg h1, if_pos h2, List.mem_cons, mem_ins]
          constructor
          · rintro (rfl | rfl | h) <;> simp_all
          · rintro (rfl | rfl | h) <;> simp_all
        · have hxz : x = z := Nat.le_antisymm (Nat.not_lt.mp h2) (Nat.not_lt.mp h1)
          subst hxz
          simp [ins, h1]

theorem ins_sortedLt {x : Nat} : ∀ {l : List Nat}, SortedLt l → SortedLt (ins x l)
  | [], _ => by simp [ins, SortedLt]
  | z :: zs, h => by
      by_cases h1 : x < z
      · show SortedLt (ins x (z :: zs))
        simp only [ins, if_pos h1]
        show (∀ y ∈ z :: zs, x < y) ∧ SortedLt (z :: zs)
        refine ⟨?_, h⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact h1
        · exact Nat.lt_trans h1 (h.1 y hy')
      · by_cases h2 : z < x
        · show SortedLt (ins x (z :: zs))
          simp only [ins, if_neg h1, if_pos h2]
          show (∀ y ∈ ins x zs, z < y) ∧ SortedLt (ins x zs)
          refine ⟨?_, ins_sortedLt h.2⟩
          intro y hy
          rcases mem_ins.mp hy with rfl | hy'
          · exact h2
          · exact h.1 y hy'
        · show SortedLt (ins x (z :: zs))
          simp only [ins, if_neg h1, if_neg h2]
          exact h

theorem canon_sortedLt : ∀ l : List Nat, SortedLt (canon l)
  | [] => by simp [canon, SortedLt]
  | x :: xs => ins_sortedLt (canon_sortedLt xs)

theorem ins_cons_of_lt_all {x : Nat} :
    ∀ {l : List Nat}, (∀ y ∈ l, x < y) → ins x l = x :: l
  | [], _ => rfl
  | z :: zs, h => by simp [ins, h z (by simp)]

theorem canon_eq_of_sortedLt : ∀ {l : List Nat}, SortedLt l → canon l = l
  | [], _ => rfl
  | x :: xs, h => by
      show ins x (canon xs) = x :: xs
      rw [canon_eq_of_sortedLt h.2, ins_cons_of_lt_all h.1]

/-- The model's analogue of `EC1-T006`. This is a fact about THIS file's
`canon`; it does not discharge `EC1-T006` for `EC1-D026`. -/
theorem canon_idem (l : List Nat) : canon (canon l) = canon l :=
  canon_eq_of_sortedLt (canon_sortedLt l)

/-! ### §2.2 — the raw carrier

`AER` is modelled by its error row alone (`A` and `R` are named and elided —
this file's theorem is about the round trip, not about the triple's shape). -/

abbrev Alt := Nat
abbrev AER := List Alt

/-- A block: the estate's `PProg` as its sequential body, plus an id, the
typed failure alternatives it may escape with, and its successor edges. -/
structure RawBlock where
  id     : Nat
  body   : PProg
  raises : List Alt
  exits  : List Nat
  deriving DecidableEq

structure RawProgram where
  entry     : Nat
  blocks    : List RawBlock
  declaredE : AER
  deriving DecidableEq

def RawProgram.ids (r : RawProgram) : List Nat := r.blocks.map (·.id)

/-! ### §2.3 — the well-formedness clauses

A NAMED SUBSET of `ALGEBRA.md` §4.3: clause 1, a fragment of clause 2, clause
10, clause 11. All four are SYNTACTIC by construction, so `PROOF-DAG.md`:221's
prohibition is not in play here. Clauses 3-9 and 12 are not modelled. -/

def NoDupN : List Nat → Prop
  | [] => True
  | x :: xs => x ∉ xs ∧ NoDupN xs

/-- Clause 1 `IdsWF`: the block table is duplicate-free and every edge resolves. -/
def IdsWF (r : RawProgram) : Prop :=
  NoDupN r.ids ∧ ∀ b ∈ r.blocks, ∀ e ∈ b.exits, e ∈ r.ids

/-- Clause 10 `EntryWF`, syntactic half: the entry resolves. -/
def EntryWF (r : RawProgram) : Prop := r.entry ∈ r.ids

/-- Clause 2 fragment `BodiesWF`, stated with the estate's own `PLine.WF`. -/
def BodiesWF (r : RawProgram) : Prop := ∀ b ∈ r.blocks, ∀ l ∈ b.body, l.WF

/-- Static synthesis of the error row: the canonical union of what the blocks
raise. A function, deliberately — see the note on `EC1-T016` at the foot. -/
def synthAER (r : RawProgram) : AER := canon (r.blocks.flatMap (·.raises))

/-- Clause 11 `AERWF`: the synthesized row IS the declared one. -/
def AERWF (r : RawProgram) : Prop := synthAER r = r.declaredE

def ProgramWF (r : RawProgram) : Prop :=
  IdsWF r ∧ EntryWF r ∧ BodiesWF r ∧ AERWF r

/-! ### §2.4 — diagnostics

Clause-named and PAYLOAD-CARRYING, in the shape of `Cas/Core/Admission.lean:29
AdmissionError` (`.wrongKind` carries expected AND actual). A `Diagnostic` is
one value, never a list: `EC1-CE031` and R16. -/

inductive Diagnostic where
  | dupBlockId (id : Nat)
  | danglingExit (source target : Nat)
  | entryUnbound (entry : Nat)
  | badLine (blockId : Nat) (line : PLine)
  | rowMismatch (synthesized declared : AER)
  deriving DecidableEq

/-! ### §2.5 — the clause layer

Structural recursion plus decidable per-clause reflection — `PROOF-DAG.md` §16's
named Checker route. Every scan is FIRST-ERROR and returns ONE diagnostic (R16),
and every scan decides the RAW input: nothing here mentions `normalizeRaw`, and
nothing here mentions `ProgramWF`, so `check_sound` below is not a projection. -/

def pinWFB : PIn → Bool
  | .lit _ => true
  | .ans i => decide (i < 4294967296)

theorem pinWFB_iff (i : PIn) : pinWFB i = true ↔ i.WF := by
  cases i <;> simp [pinWFB, PIn.WF]

def plineWFB : PLine → Bool
  | .put _ _ payload refs =>
      decide (payload.length < 4294967296) && decide (refs.length < 4294967296) &&
        refs.all (fun r => pinWFB r.2)
  | .load src => pinWFB src

theorem plineWFB_iff (l : PLine) : plineWFB l = true ↔ l.WF := by
  cases l with
  | put v t payload refs =>
      simp [plineWFB, PLine.WF, List.all_eq_true, pinWFB_iff, and_assoc]
  | load src => simp [plineWFB, PLine.WF, pinWFB_iff]

def checkNoDup : List Nat → Option Diagnostic
  | [] => none
  | x :: xs => if x ∈ xs then some (.dupBlockId x) else checkNoDup xs

theorem checkNoDup_none_iff : ∀ l : List Nat, checkNoDup l = none ↔ NoDupN l
  | [] => by simp [checkNoDup, NoDupN]
  | x :: xs => by
      by_cases h : x ∈ xs
      · simp [checkNoDup, NoDupN, h]
      · simp [checkNoDup, NoDupN, h, checkNoDup_none_iff xs]

def checkExitsOne (src : Nat) (ids : List Nat) : List Nat → Option Diagnostic
  | [] => none
  | e :: es => if e ∈ ids then checkExitsOne src ids es else some (.danglingExit src e)

theorem checkExitsOne_none_iff (src : Nat) (ids : List Nat) :
    ∀ es : List Nat, checkExitsOne src ids es = none ↔ ∀ e ∈ es, e ∈ ids
  | [] => by simp [checkExitsOne]
  | e :: es => by
      by_cases h : e ∈ ids
      · simp [checkExitsOne, h, checkExitsOne_none_iff src ids es]
      · simp [checkExitsOne, h]

def checkExits (ids : List Nat) : List RawBlock → Option Diagnostic
  | [] => none
  | b :: bs =>
    match checkExitsOne b.id ids b.exits with
    | some d => some d
    | none => checkExits ids bs

theorem checkExits_none_iff (ids : List Nat) :
    ∀ bs : List RawBlock, checkExits ids bs = none ↔ ∀ b ∈ bs, ∀ e ∈ b.exits, e ∈ ids
  | [] => by simp [checkExits]
  | b :: bs => by
      cases h : checkExitsOne b.id ids b.exits with
      | some d =>
          have hno : ¬ ∀ e ∈ b.exits, e ∈ ids := by
            intro hall
            rw [(checkExitsOne_none_iff b.id ids b.exits).mpr hall] at h
            exact nomatch h
          have hstep : checkExits ids (b :: bs) = some d := by simp [checkExits, h]
          rw [hstep]
          constructor
          · intro hcon; exact nomatch hcon
          · intro hall; exact absurd (hall b (by simp)) hno
      | none =>
          have hb := (checkExitsOne_none_iff b.id ids b.exits).mp h
          have hstep : checkExits ids (b :: bs) = checkExits ids bs := by
            simp [checkExits, h]
          rw [hstep, checkExits_none_iff ids bs]
          constructor
          · intro hall b' hb' e he
            rcases List.mem_cons.mp hb' with rfl | hb''
            · exact hb e he
            · exact hall b' hb'' e he
          · intro hall b' hb' e he
            exact hall b' (List.mem_cons_of_mem _ hb') e he

def checkBodyLines (bid : Nat) : PProg → Option Diagnostic
  | [] => none
  | l :: ls => if plineWFB l then checkBodyLines bid ls else some (.badLine bid l)

theorem checkBodyLines_none_iff (bid : Nat) :
    ∀ ls : PProg, checkBodyLines bid ls = none ↔ ∀ l ∈ ls, l.WF
  | [] => by simp [checkBodyLines]
  | l :: ls => by
      by_cases h : plineWFB l = true
      · have hstep : checkBodyLines bid (l :: ls) = checkBodyLines bid ls := by
          simp [checkBodyLines, h]
        rw [hstep, checkBodyLines_none_iff bid ls]
        constructor
        · intro hall l' hl'
          rcases List.mem_cons.mp hl' with rfl | hl''
          · exact (plineWFB_iff _).mp h
          · exact hall l' hl''
        · intro hall l' hl'
          exact hall l' (List.mem_cons_of_mem _ hl')
      · have hstep : checkBodyLines bid (l :: ls) = some (.badLine bid l) := by
          simp [checkBodyLines, h]
        rw [hstep]
        constructor
        · intro hcon; exact nomatch hcon
        · intro hall; exact absurd ((plineWFB_iff l).mpr (hall l (by simp))) h

def checkBodies : List RawBlock → Option Diagnostic
  | [] => none
  | b :: bs =>
    match checkBodyLines b.id b.body with
    | some d => some d
    | none => checkBodies bs

theorem checkBodies_none_iff :
    ∀ bs : List RawBlock, checkBodies bs = none ↔ ∀ b ∈ bs, ∀ l ∈ b.body, l.WF
  | [] => by simp [checkBodies]
  | b :: bs => by
      cases h : checkBodyLines b.id b.body with
      | some d =>
          have hno : ¬ ∀ l ∈ b.body, l.WF := by
            intro hall
            rw [(checkBodyLines_none_iff b.id b.body).mpr hall] at h
            exact nomatch h
          have hstep : checkBodies (b :: bs) = some d := by simp [checkBodies, h]
          rw [hstep]
          constructor
          · intro hcon; exact nomatch hcon
          · intro hall; exact absurd (hall b (by simp)) hno
      | none =>
          have hb := (checkBodyLines_none_iff b.id b.body).mp h
          have hstep : checkBodies (b :: bs) = checkBodies bs := by simp [checkBodies, h]
          rw [hstep, checkBodies_none_iff bs]
          constructor
          · intro hall b' hb' l' hl'
            rcases List.mem_cons.mp hb' with rfl | hb''
            · exact hb l' hl'
            · exact hall b' hb'' l' hl'
          · intro hall b' hb' l' hl'
            exact hall b' (List.mem_cons_of_mem _ hb') l' hl'

def checkIds (r : RawProgram) : Option Diagnostic :=
  match checkNoDup r.ids with
  | some d => some d
  | none => checkExits r.ids r.blocks

theorem checkIds_none_iff (r : RawProgram) : checkIds r = none ↔ IdsWF r := by
  cases h : checkNoDup r.ids with
  | some d =>
      have hno : ¬ NoDupN r.ids := by
        intro hn
        rw [(checkNoDup_none_iff r.ids).mpr hn] at h
        exact nomatch h
      have hstep : checkIds r = some d := by simp [checkIds, h]
      rw [hstep]
      constructor
      · intro hcon; exact nomatch hcon
      · intro hwf; exact absurd hwf.1 hno
  | none =>
      have hnd : NoDupN r.ids := (checkNoDup_none_iff r.ids).mp h
      have hstep : checkIds r = checkExits r.ids r.blocks := by simp [checkIds, h]
      rw [hstep, checkExits_none_iff r.ids r.blocks]
      exact ⟨fun hall => ⟨hnd, hall⟩, fun hwf => hwf.2⟩

def checkEntry (r : RawProgram) : Option Diagnostic :=
  if r.entry ∈ r.ids then none else some (.entryUnbound r.entry)

theorem checkEntry_none_iff (r : RawProgram) : checkEntry r = none ↔ EntryWF r := by
  by_cases h : r.entry ∈ r.ids <;> simp [checkEntry, EntryWF, h]

def checkAER (r : RawProgram) : Option Diagnostic :=
  if synthAER r = r.declaredE then none
  else some (.rowMismatch (synthAER r) r.declaredE)

theorem checkAER_none_iff (r : RawProgram) : checkAER r = none ↔ AERWF r := by
  by_cases h : synthAER r = r.declaredE <;> simp [checkAER, AERWF, h]

/-- The frozen clause order (R16): `IdsWF`, `EntryWF`, `BodiesWF`, `AERWF`.
`IdsWF` first is not cosmetic — see §2.11. -/
def checkClauses (r : RawProgram) : Option Diagnostic :=
  match checkIds r with
  | some d => some d
  | none =>
    match checkEntry r with
    | some d => some d
    | none =>
      match checkBodies r.blocks with
      | some d => some d
      | none => checkAER r

/-- The clause layer decides exactly `ProgramWF`, on the RAW input. Both
directions in one `iff`, the house shape of `Cas/Core/Admission.lean:60
checkRefs_ok_iff`. `.mp` is `EC1-T010`'s content; `.mpr` is `EC1-T011`'s. -/
theorem checkClauses_none_iff (r : RawProgram) :
    checkClauses r = none ↔ ProgramWF r := by
  cases hi : checkIds r with
  | some d =>
      have hno : ¬ IdsWF r := fun h => by
        rw [(checkIds_none_iff r).mpr h] at hi; exact nomatch hi
      have hstep : checkClauses r = some d := by simp [checkClauses, hi]
      rw [hstep]
      constructor
      · intro hcon; exact nomatch hcon
      · intro hwf; exact absurd hwf.1 hno
  | none =>
      have hI : IdsWF r := (checkIds_none_iff r).mp hi
      cases he : checkEntry r with
      | some d =>
          have hno : ¬ EntryWF r := fun h => by
            rw [(checkEntry_none_iff r).mpr h] at he; exact nomatch he
          have hstep : checkClauses r = some d := by simp [checkClauses, hi, he]
          rw [hstep]
          constructor
          · intro hcon; exact nomatch hcon
          · intro hwf; exact absurd hwf.2.1 hno
      | none =>
          have hE : EntryWF r := (checkEntry_none_iff r).mp he
          cases hb : checkBodies r.blocks with
          | some d =>
              have hno : ¬ BodiesWF r := fun h => by
                rw [(checkBodies_none_iff r.blocks).mpr h] at hb; exact nomatch hb
              have hstep : checkClauses r = some d := by
                simp [checkClauses, hi, he, hb]
              rw [hstep]
              constructor
              · intro hcon; exact nomatch hcon
              · intro hwf; exact absurd hwf.2.2.1 hno
          | none =>
              have hB : BodiesWF r := (checkBodies_none_iff r.blocks).mp hb
              have hstep : checkClauses r = checkAER r := by
                simp [checkClauses, hi, he, hb]
              rw [hstep, checkAER_none_iff r]
              exact ⟨fun hA => ⟨hI, hE, hB, hA⟩, fun hwf => hwf.2.2.2⟩

/-! ### §2.6 — the raw normalizer

`normalizeRaw` canonicalizes the DECLARED row. It is a real normalizer: §2.11
exhibits a program it repairs, which is exactly why `check` may not run it
first. -/

def normalizeRaw (r : RawProgram) : RawProgram :=
  { r with declaredE := canon r.declaredE }

/-- The model's `EC1-T006`. Again: a fact about this file, not a discharge of
the packet row. -/
theorem normalizeRaw_idem (r : RawProgram) :
    normalizeRaw (normalizeRaw r) = normalizeRaw r := by
  simp [normalizeRaw, canon_idem]

/-- Normalization does not move the synthesized row. Needed for the Sigma index. -/
theorem synthAER_normalizeRaw (r : RawProgram) :
    synthAER (normalizeRaw r) = synthAER r := rfl

/-- Normalization PRESERVES well-formedness. This is the direction that holds;
§2.11 refutes the other one. -/
theorem programWF_normalizeRaw {r : RawProgram} (h : ProgramWF r) :
    ProgramWF (normalizeRaw r) := by
  obtain ⟨hI, hE, hB, hA⟩ := h
  refine ⟨hI, hE, hB, ?_⟩
  show synthAER r = canon r.declaredE
  rw [← hA]
  exact (canon_idem _).symm

/-! ### §2.7 — the checked carrier

Design (B), the packet's own: the stored raw is already normal
(`CONTRACT-PACKET.md`:309, `EC1-K10`). Every field beyond `raw` is a `Prop`,
which is what buys `ext` — and §2.10 proves that is not a stylistic choice. -/

structure CheckedProgram (aer : AER) where
  raw       : RawProgram
  wf        : ProgramWF raw
  canonical : normalizeRaw raw = raw
  aerOk     : synthAER raw = aer

def erase {aer : AER} (p : CheckedProgram aer) : RawProgram := p.raw

/-- `EC1-T014`, as it actually is: a field selector. No checker in scope. -/
theorem erase_wf {aer : AER} (p : CheckedProgram aer) : ProgramWF (erase p) := p.wf

/-- `EC1-K10` (`CONTRACT-PACKET.md`:309), as it actually is: a field selector. -/
theorem erase_normal {aer : AER} (p : CheckedProgram aer) :
    normalizeRaw (erase p) = erase p := p.canonical

/-- `EC1-T017 checked_aer_exact`, as it actually is: a field selector. -/
theorem checked_aer_exact {aer : AER} (p : CheckedProgram aer) :
    synthAER (erase p) = aer := p.aerOk

/-- Extensionality. Free because every non-`raw` field is a `Prop`. -/
theorem CheckedProgram.ext {aer : AER} {p q : CheckedProgram aer}
    (h : p.raw = q.raw) : p = q := by
  cases p; cases q; cases h; rfl

/-- A `Sigma` of checked programs is determined by the raw alone: the index is
recovered from `aerOk`. This is the transport every proof of the row needs. -/
theorem sigma_ext {a a' : AER} (p : CheckedProgram a) (q : CheckedProgram a')
    (h : p.raw = q.raw) : (⟨a, p⟩ : Σ x, CheckedProgram x) = ⟨a', q⟩ := by
  have ha : a = a' := by rw [← p.aerOk, ← q.aerOk, h]
  subst ha
  exact congrArg _ (CheckedProgram.ext h)

/-! ### §2.8 — the checker

`check` branches on the CLAUSE LAYER's own verdict, never on `decide (ProgramWF
r)`; `checkClauses` is defined without reference to `ProgramWF`, so
`check_sound` below reconnects two independently defined objects instead of
projecting one. The normalizer sits INSIDE the payload, strictly after the
decision — the order obligation, forced by §2.11. -/

def mkChecked (r : RawProgram) (h : ProgramWF r) : CheckedProgram (synthAER r) :=
  { raw := normalizeRaw r
  , wf := programWF_normalizeRaw h
  , canonical := normalizeRaw_idem r
  , aerOk := synthAER_normalizeRaw r }

def firstDiag (r : RawProgram) : Diagnostic :=
  (checkClauses r).getD (.rowMismatch (synthAER r) r.declaredE)

def check (r : RawProgram) : Except Diagnostic (Σ aer, CheckedProgram aer) :=
  if hc : checkClauses r = none then
    .ok ⟨synthAER r, mkChecked r ((checkClauses_none_iff r).mp hc)⟩
  else
    .error (firstDiag r)

/-- `EC1-T010`. -/
theorem check_sound {r : RawProgram} {a : AER} {p : CheckedProgram a}
    (h : check r = .ok ⟨a, p⟩) : ProgramWF r := by
  by_cases hc : checkClauses r = none
  · exact (checkClauses_none_iff r).mp hc
  · rw [check, dif_neg hc] at h; exact nomatch h

/-- `EC1-T011`, with the index EXISTENTIALLY bound. The DAG's spelling leaves
`a` free; under universal closure that row is false as soon as the index type
has two inhabitants, and under existential closure it says only "accepted". -/
theorem check_complete {r : RawProgram} (h : ProgramWF r) :
    ∃ (a : AER) (p : CheckedProgram a), check r = .ok ⟨a, p⟩ := by
  have hc : checkClauses r = none := (checkClauses_none_iff r).mpr h
  exact ⟨synthAER r, mkChecked r ((checkClauses_none_iff r).mp hc),
    by rw [check, dif_pos hc]⟩

/-- Evaluation lemma: the payload on a well-formed input, on the nose. -/
theorem check_ok_of_wf {r : RawProgram} (h : ProgramWF r) :
    check r = .ok ⟨synthAER r, mkChecked r h⟩ := by
  have hc : checkClauses r = none := (checkClauses_none_iff r).mpr h
  rw [check, dif_pos hc]

/-- The unlisted companion the DAG does not row: a successful check erases back
to the normalized raw it was given. Without it the row cannot pin its payload. -/
theorem erase_check {r : RawProgram} {a : AER} {q : CheckedProgram a}
    (h : check r = .ok ⟨a, q⟩) : erase q = normalizeRaw r := by
  have hwf : ProgramWF r := check_sound h
  rw [check_ok_of_wf hwf] at h
  exact (congrArg (fun s : Σ x, CheckedProgram x => s.2.raw) (Except.ok.inj h)).symm

/-- `EC1-T012`, free from `EC1-T010` and `EC1-T011`; no decidability premise is
used and none is available to use. -/
theorem check_error_iff (r : RawProgram) :
    (∃ d, check r = .error d) ↔ ¬ ProgramWF r := by
  constructor
  · rintro ⟨d, hd⟩ hwf
    rw [check_ok_of_wf hwf] at hd
    exact nomatch hd
  · intro hn
    refine ⟨firstDiag r, ?_⟩
    have hc : checkClauses r ≠ none := fun hc => hn ((checkClauses_none_iff r).mp hc)
    rw [check, dif_neg hc]

/-! ### §2.9 — `EC1-T013`

`normalizeChecked` is declared INDEPENDENTLY of `check` — it mentions only
`normalizeRaw` — which is what keeps the row out of §1.1's tautology class. -/

def normalizeChecked {aer : AER} (p : CheckedProgram aer) : CheckedProgram aer :=
  { raw := normalizeRaw p.raw
  , wf := programWF_normalizeRaw p.wf
  , canonical := normalizeRaw_idem p.raw
  , aerOk := (synthAER_normalizeRaw p.raw).trans p.aerOk }

/-- **`EC1-T013`**, at this carrier, in the DAG's own spelling.

Two things the schematic signature hides. The `rfl` is `normalizeRaw (erase p) =
normalizeRaw p.raw`, so THIS spelling of the row does not consume `EC1-K10` at
all — only `check_erase_id` below does. And the proof route runs through
`p.wf` (`EC1-T014`, a projection) and `check_ok_of_wf` (`EC1-T011`); it never
touches `EC1-T010`, which the DAG lists as its dependency. `EC1-T006` enters
invisibly, inside `check`: see the header. -/
theorem check_erase {aer : AER} (p : CheckedProgram aer) :
    check (erase p) = .ok ⟨aer, normalizeChecked p⟩ := by
  rw [check_ok_of_wf (r := erase p) p.wf]
  exact congrArg Except.ok (sigma_ext _ _ rfl)

/-- §1.4 landing at this carrier: the row's normalizer IS the identity, so the
honest spelling of `EC1-T013` is the next theorem and `normalizeChecked` is a
phantom term. -/
theorem normalizeChecked_eq_self {aer : AER} (p : CheckedProgram aer) :
    normalizeChecked p = p :=
  CheckedProgram.ext p.canonical

/-- **`EC1-T013`, honest spelling.** -/
theorem check_erase_id {aer : AER} (p : CheckedProgram aer) :
    check (erase p) = .ok ⟨aer, p⟩ := by
  rw [check_erase p, normalizeChecked_eq_self p]

/-- The checked-level twin of `EC1-T006`, owed by nobody in the DAG. Here it is
immediate, because the normalizer is the identity. -/
theorem normalizeChecked_idem {aer : AER} (p : CheckedProgram aer) :
    normalizeChecked (normalizeChecked p) = normalizeChecked p := by
  rw [normalizeChecked_eq_self, normalizeChecked_eq_self]

/-! ### §2.10 — REFUTATION: a carrier that discards data kills the row

`ALGEBRA.md`:319 says `CheckedProgram` "stores an erased raw value, normalized
lookup tables, and evidence of `ProgramWF`". "Normalized lookup tables" is a
non-`Prop` field. If ANY such field is not recomputable from the raw, no checker
whatsoever satisfies the row in its honest spelling — this is §1.5 made
concrete, and it is a fact about every possible `check`, not about mine. -/

structure CheckedPlus (aer : AER) where
  raw       : RawProgram
  wf        : ProgramWF raw
  canonical : normalizeRaw raw = raw
  aerOk     : synthAER raw = aer
  note      : Bool

def erasePlus {aer : AER} (p : CheckedPlus aer) : RawProgram := p.raw

/-- One block, no lines, no raises, no exits: admitted, and already normal. -/
def good : RawProgram := { entry := 0, blocks := [⟨0, [], [], []⟩], declaredE := [] }

theorem good_wf : ProgramWF good :=
  (checkClauses_none_iff good).mp rfl

theorem good_canonical : normalizeRaw good = good := rfl

theorem good_aer : synthAER good = ([] : AER) := rfl

def cpTrue : CheckedPlus ([] : AER) := ⟨good, good_wf, good_canonical, good_aer, true⟩
def cpFalse : CheckedPlus ([] : AER) := ⟨good, good_wf, good_canonical, good_aer, false⟩

/-- REFUTED. No checker into `CheckedPlus` satisfies `EC1-T013`'s honest
spelling. The two witnesses are admitted, normal, and erase to the same raw. -/
theorem no_checker_satisfies_check_erase_on_CheckedPlus
    (chk : RawProgram → Except Diagnostic (Σ a, CheckedPlus a)) :
    ¬ (∀ (a : AER) (p : CheckedPlus a), chk (erasePlus p) = .ok ⟨a, p⟩) := by
  intro hT
  have h1 := hT [] cpTrue
  have h2 := hT [] cpFalse
  rw [show erasePlus cpTrue = erasePlus cpFalse from rfl, h2] at h1
  have heq : cpTrue = cpFalse := sigma_same_index (Except.ok.inj h1).symm
  have hb : (true : Bool) = false := congrArg CheckedPlus.note heq
  exact Bool.noConfusion hb

/-- The positive face of the same fact, and the price the row pays: with a
non-identity `normalizeChecked` the row is satisfiable at `CheckedPlus`, but
only by a normalizer that FORGETS the field. `normalizeChecked` is then not a
normalizer, it is a data-destroying projection. -/
theorem check_erase_forces_the_extra_field_to_be_forgotten
    (chk : RawProgram → Except Diagnostic (Σ a, CheckedPlus a))
    (nc : ∀ a, CheckedPlus a → CheckedPlus a)
    (T013 : ∀ (a : AER) (p : CheckedPlus a), chk (erasePlus p) = .ok ⟨a, nc a p⟩) :
    (nc [] cpTrue).note = (nc [] cpFalse).note :=
  congrArg CheckedPlus.note
    (normalizeChecked_factors_through_erase chk (fun _ p => erasePlus p) nc T013
      cpTrue cpFalse rfl)

/-! ### §2.11 — the order obligation: `check` may not normalize first

`EC1-CE030`'s phenomenon at this carrier. Normalization does not preserve the
row clause, it CREATES it — the same fact as `Cas/Backend/Canon.lean:167
nodup_keys_canonServices`, which is why `EC1-CE030` forces a duplicate-free
premise on row normalization (R16 part 2). So `ProgramWF (normalizeRaw r) -> ProgramWF r` is
FALSE, and a `check` that normalizes before it decides establishes nothing about
`r`, which is exactly what `EC1-T010`'s conclusion is about. `EC1-T013` inherits
the constraint through the `wf` field of the very `p` it quantifies over. -/

def ce030 : RawProgram := { entry := 0, blocks := [⟨0, [], [1], []⟩], declaredE := [1, 1] }

theorem ce030_repaired_by_normalization : AERWF (normalizeRaw ce030) := rfl

theorem ce030_raw_is_condemned : ¬ AERWF ce030 := by
  intro h
  exact absurd (congrArg (fun l : AER => l.length) h) (by decide)

theorem programWF_normalizeRaw_is_not_reversible :
    ¬ ∀ r : RawProgram, ProgramWF (normalizeRaw r) → ProgramWF r := by
  intro hall
  exact ce030_raw_is_condemned (hall ce030 ((checkClauses_none_iff _).mp rfl)).2.2.2

/-- And the checker this file ships does decide the raw: `ce030` is refused,
with the clause-named, payload-carrying diagnostic. -/
theorem check_refuses_ce030 :
    check ce030 = .error (.rowMismatch [1] [1, 1]) := rfl

/-! ### §2.12 — the DAG's `T013 <-> T014` cycle

`PROOF-DAG.md`:215-216 has `T013 deps T006,T010` and `T014 deps T010,T013`,
while `T013`'s success premise IS `ProgramWF (erase p)`, i.e. `T014`. The cycle
dissolves because `T014` is not a theorem: `erase_wf` above is `p.wf`. This
file's `check_erase` consumes `p.wf` directly and never consumes `EC1-T010`. -/

theorem erase_wf_is_the_field {aer : AER} (p : CheckedProgram aer) :
    erase_wf p = p.wf := rfl

/-! ### §2.13 — a note on `EC1-T016`, recorded because this row rides on it

`EC1-T013`'s Sigma index is exact only if the synthesized index is pinned by
something other than a Lean function's own determinism. `synthAER` here IS a
function, and under that reading `EC1-T016` proves nothing: the `ProgramWF`
premise is never consumed. -/

theorem T016_premise_is_dead {Raw Idx : Type} (f : Raw → Idx) (WF : Raw → Prop) :
    ∀ r, WF r → ∃ a, f r = a ∧ ∀ b, f r = b → b = a :=
  fun _ _ => ⟨f _, rfl, fun _ h => h.symm⟩

end EffectCoreT013

/-! ## Kernel receipts -/

#print axioms EffectCoreT013.check_erase_is_vacuous_under_a_checker_derived_normalizer
#print axioms EffectCoreT013.sigma_same_index
#print axioms EffectCoreT013.normalizeChecked_factors_through_erase
#print axioms EffectCoreT013.normalizeChecked_preserves_erasure
#print axioms EffectCoreT013.normalizeChecked_is_forced_to_be_the_identity
#print axioms EffectCoreT013.check_erase_id_forces_erase_injective
#print axioms EffectCoreT013.check_erase_entails_index_exactness
#print axioms EffectCoreT013.erase_wf_is_a_projection
#print axioms EffectCoreT013.mem_ins
#print axioms EffectCoreT013.ins_sortedLt
#print axioms EffectCoreT013.canon_sortedLt
#print axioms EffectCoreT013.ins_cons_of_lt_all
#print axioms EffectCoreT013.canon_eq_of_sortedLt
#print axioms EffectCoreT013.canon_idem
#print axioms EffectCoreT013.pinWFB_iff
#print axioms EffectCoreT013.plineWFB_iff
#print axioms EffectCoreT013.checkNoDup_none_iff
#print axioms EffectCoreT013.checkExitsOne_none_iff
#print axioms EffectCoreT013.checkExits_none_iff
#print axioms EffectCoreT013.checkBodyLines_none_iff
#print axioms EffectCoreT013.checkBodies_none_iff
#print axioms EffectCoreT013.checkIds_none_iff
#print axioms EffectCoreT013.checkEntry_none_iff
#print axioms EffectCoreT013.checkAER_none_iff
#print axioms EffectCoreT013.checkClauses_none_iff
#print axioms EffectCoreT013.normalizeRaw_idem
#print axioms EffectCoreT013.synthAER_normalizeRaw
#print axioms EffectCoreT013.programWF_normalizeRaw
#print axioms EffectCoreT013.erase_wf
#print axioms EffectCoreT013.erase_normal
#print axioms EffectCoreT013.checked_aer_exact
#print axioms EffectCoreT013.CheckedProgram.ext
#print axioms EffectCoreT013.sigma_ext
#print axioms EffectCoreT013.check_sound
#print axioms EffectCoreT013.check_complete
#print axioms EffectCoreT013.check_ok_of_wf
#print axioms EffectCoreT013.erase_check
#print axioms EffectCoreT013.check_error_iff
#print axioms EffectCoreT013.check_erase
#print axioms EffectCoreT013.normalizeChecked_eq_self
#print axioms EffectCoreT013.check_erase_id
#print axioms EffectCoreT013.normalizeChecked_idem
#print axioms EffectCoreT013.good_wf
#print axioms EffectCoreT013.good_canonical
#print axioms EffectCoreT013.good_aer
#print axioms EffectCoreT013.no_checker_satisfies_check_erase_on_CheckedPlus
#print axioms EffectCoreT013.check_erase_forces_the_extra_field_to_be_forgotten
#print axioms EffectCoreT013.ce030_repaired_by_normalization
#print axioms EffectCoreT013.ce030_raw_is_condemned
#print axioms EffectCoreT013.programWF_normalizeRaw_is_not_reversible
#print axioms EffectCoreT013.check_refuses_ce030
#print axioms EffectCoreT013.erase_wf_is_the_field
#print axioms EffectCoreT013.T016_premise_is_dead
