import Cas.Backend.Canon

/-!
# Attack on `EC1-T016` — breaker pass

Target: `.staging/effect-core-v1/workshop/s2/T016.lean`, claimed outcome
REFUTED, recommendation "delete `EC1-T016` from `PROOF-DAG.md:218`".

Run it:

```
cd /Users/pooks/Dev/foldlab/library/cas && \
  lake env lean ../../.staging/effect-core-v1/workshop/s2/attack-EC1-T016.lean
```

## What survives the attack

The target file re-elaborates: exit 0, zero errors, zero warnings, 36 theorems,
36 `#print axioms` receipts, no `sorry`/`axiom`/`native_decide`/`#eval`. The
counts it reports are ACCURATE (37 `theorem` greps, one of which is prose at
line 72). `#check @ExistsUnique` really is `Unknown identifier` on
`leanprover/lean4:v4.33.1` here, so the hand-rolled `ExistsUnique'` is
warranted and is spelled faithfully. `SynthAER` really does occur exactly twice
packet-wide, both inside `PROOF-DAG.md:218-219`, and really is absent from the
`PROPOSED TERM` list. Reading A's tautology result is robust: it is quantified
over an ARBITRARY premise predicate and an ARBITRARY synthesizer, so no
strengthening of `ProgramWF` and no choice of synthesizer can escape it.

## What does not survive

Four breaks, all proved below.

* **§A — the exhaustiveness claim is FALSE.** The report says "every candidate
  `SynthAER` falls in one of the two classes, and both are closed". There is a
  third class, and a sibling in this same directory already built it:
  `T017.lean:668` declares a `Prop`-valued `SynthAER` and `T017.lean:621`
  `synthRow_unique` proves it single-valued by antisymmetry of leastness, not
  by `rfl`. §A exhibits that class at the TARGET's own carrier: under it
  `EC1-T016` as written is TRUE, its proof is `ascending_ext` rather than
  `rfl`, and the specification REFUSES rows. So the recommendation "delete
  `EC1-T016`" does not follow from the file's own results.
* **§B — the transfer argument is BACKWARDS.** The report says its two-clause
  `ProgramWF` is weaker than the packet's twelve-clause one and that this
  "STRENGTHENS the refutation". Refutation is ANTI-monotone in the premise. §B
  exhibits a non-degenerate, inhabited strengthening of the target's own
  `ProgramWF` under which the reading-B row is TRUE. Result 2 therefore holds
  at the two-clause carrier only; its transfer to the packet's `ProgramWF` is
  an assumption, not a result.
* **§C — `AERWF` puts `canon` on the side `ALGEBRA.md:316` does not.** That
  line reads "synthesized `A/E/R` NORMALIZES TO the declared triple", i.e.
  `canon (synth) = declared`. The target models `canon (declared) = synth`.
  Because `synthE` is already canonical, the literal reading collapses to plain
  equality — under which `RowsWF` is DERIVABLE, the target's
  `agreement_needs_RowsWF` witness is not a counterexample, and
  `aer_synthesis_agrees` is a restatement of its own hypothesis. Result 5's
  "both conjuncts independently necessary" is an artifact of the non-literal
  side-choice.
* **§D — Result 5's premise is not "live" either.** At the target's OWN
  spelling `ProgramWF r <-> r.declaredE = synthE r` (`D1`). The converse holds,
  so `aer_synthesis_agrees` is the forward half of a biconditional — the two
  clauses re-spelled as one equation, not `AERWF` "becoming DERIVABLE". Useful
  as a normalization result; not the contrast with §3/§6 the report draws.

§F runs the falsifier battery. `#print axioms` follows every theorem. No
`sorry`, no `axiom`, no `native_decide`, no `#eval` standing for a claim.
Nothing here is imported from the target; the carrier is re-declared so the
attack is self-contained and cannot inherit a defect by construction.
-/

namespace AttackT016

/-! ## §0 — the target's carrier, re-declared verbatim

Copied from `T016.lean` §2 so every attack below is stated against exactly the
definitions the target uses. The support lemmas are re-proved, not assumed. -/

abbrev Tag := Nat

structure RawOp where
  tag : Tag
deriving DecidableEq, Repr

structure RawProgram where
  ops : List RawOp
  declaredE : List Tag
deriving DecidableEq, Repr

def Contributes (r : RawProgram) (t : Tag) : Prop := ∃ o ∈ r.ops, o.tag = t

abbrev Ascending (l : List Tag) : Prop := l.Pairwise (· < ·)

theorem ascending_cons {x : Tag} {xs : List Tag} :
    Ascending (x :: xs) ↔ (∀ y ∈ xs, x < y) ∧ Ascending xs := List.pairwise_cons

def ins (x : Tag) : List Tag → List Tag
  | [] => [x]
  | y :: ys => if x = y then y :: ys else if x < y then x :: y :: ys else y :: ins x ys

def canon : List Tag → List Tag
  | [] => []
  | x :: xs => ins x (canon xs)

theorem ins_self (x : Tag) (ys : List Tag) : ins x (x :: ys) = x :: ys := by
  simp [ins]

theorem mem_ins (x t : Tag) : ∀ l : List Tag, t ∈ ins x l ↔ t = x ∨ t ∈ l
  | [] => by simp [ins]
  | y :: ys => by
      by_cases hxy : x = y
      · subst hxy; simp [ins]
      · by_cases hlt : x < y
        · simp [ins, hxy, hlt]
        · have ih := mem_ins x t ys
          simp only [ins, if_neg hxy, if_neg hlt, List.mem_cons, ih]
          constructor
          · rintro (rfl | rfl | hm)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hm)
          · rintro (rfl | rfl | hm)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hm)

theorem ascending_ins (x : Tag) : ∀ l : List Tag, Ascending l → Ascending (ins x l)
  | [], _ => by simp [ins]
  | y :: ys, h => by
      rw [ascending_cons] at h
      by_cases hxy : x = y
      · subst hxy
        rw [ins_self]
        exact ascending_cons.mpr h
      · by_cases hlt : x < y
        · rw [ins, if_neg hxy, if_pos hlt, ascending_cons]
          refine ⟨?_, ascending_cons.mpr h⟩
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact hlt
          · exact Nat.lt_trans hlt (h.1 z hz')
        · have hyx : y < x :=
            Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) (fun e => hxy e.symm)
          rw [ins, if_neg hxy, if_neg hlt, ascending_cons]
          refine ⟨?_, ascending_ins x ys h.2⟩
          intro z hz
          rcases (mem_ins x z ys).mp hz with rfl | hz'
          · exact hyx
          · exact h.1 z hz'

theorem mem_canon (t : Tag) : ∀ l : List Tag, t ∈ canon l ↔ t ∈ l
  | [] => by simp [canon]
  | x :: xs => by
      have ih := mem_canon t xs
      rw [canon, mem_ins, ih, List.mem_cons]

theorem ascending_canon : ∀ l : List Tag, Ascending (canon l)
  | [] => by simp [canon]
  | x :: xs => ascending_ins x (canon xs) (ascending_canon xs)

theorem ascending_ext : ∀ {a b : List Tag}, Ascending a → Ascending b →
    (∀ t, t ∈ a ↔ t ∈ b) → a = b
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, h => absurd ((h y).mpr (by simp)) (by simp)
  | x :: xs, [], _, _, h => absurd ((h x).mp (by simp)) (by simp)
  | x :: xs, y :: ys, ha, hb, h => by
      rw [ascending_cons] at ha hb
      have hxy : x = y := by
        by_cases hne : x = y
        · exact hne
        · exfalso
          have hx : x ∈ ys := by
            rcases List.mem_cons.mp ((h x).mp (by simp)) with e | e
            · exact absurd e hne
            · exact e
          have hy : y ∈ xs := by
            rcases List.mem_cons.mp ((h y).mpr (by simp)) with e | e
            · exact absurd e.symm hne
            · exact e
          exact Nat.lt_irrefl x (Nat.lt_trans (ha.1 y hy) (hb.1 x hx))
      subst hxy
      have htl : ∀ t, t ∈ xs ↔ t ∈ ys := by
        intro t
        constructor
        · intro ht
          rcases List.mem_cons.mp ((h t).mp (by simp [ht])) with e | e
          · exact absurd (e ▸ ha.1 t ht) (Nat.lt_irrefl x)
          · exact e
        · intro ht
          rcases List.mem_cons.mp ((h t).mpr (by simp [ht])) with e | e
          · exact absurd (e ▸ hb.1 t ht) (Nat.lt_irrefl x)
          · exact e
      exact congrArg (x :: ·) (ascending_ext ha.2 hb.2 htl)

theorem canon_of_ascending {l : List Tag} (h : Ascending l) : canon l = l :=
  ascending_ext (ascending_canon l) h (fun t => mem_canon t l)

theorem canon_idem (l : List Tag) : canon (canon l) = canon l :=
  canon_of_ascending (ascending_canon l)

def synthE (r : RawProgram) : List Tag := canon (r.ops.map RawOp.tag)

def RowsWF (r : RawProgram) : Prop := Ascending r.declaredE

def AERWF (r : RawProgram) : Prop := canon r.declaredE = synthE r

def ProgramWF (r : RawProgram) : Prop := RowsWF r ∧ AERWF r

def ExistsUnique' {α : Type} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ ∀ y, p y → y = x

def SynthE (r : RawProgram) (e : List Tag) : Prop :=
  ∀ t, Contributes r t ↔ t ∈ e

def dupProg : RawProgram := { ops := [⟨7⟩], declaredE := [7] }
def permProg : RawProgram := { ops := [⟨7⟩, ⟨9⟩], declaredE := [7, 9] }
def declPerm : RawProgram := { ops := [⟨7⟩, ⟨9⟩], declaredE := [9, 7] }

theorem dupProg_wf : ProgramWF dupProg := ⟨by simp [RowsWF, dupProg], rfl⟩

theorem dup_sol_one : SynthE dupProg [7] := by
  intro t
  constructor
  · rintro ⟨o, ho, rfl⟩; simp [dupProg] at ho; simp [ho]
  · intro ht; simp at ht; exact ⟨⟨7⟩, by simp [dupProg], by simp [ht]⟩

theorem dup_sol_two : SynthE dupProg [7, 7] := by
  intro t
  constructor
  · rintro ⟨o, ho, rfl⟩; simp [dupProg] at ho; simp [ho]
  · intro ht; simp at ht; exact ⟨⟨7⟩, by simp [dupProg], by simp [ht]⟩

theorem synthE_is_a_solution (r : RawProgram) : SynthE r (synthE r) := by
  intro t
  rw [synthE, mem_canon]
  constructor
  · rintro ⟨o, ho, rfl⟩; exact List.mem_map.mpr ⟨o, ho, rfl⟩
  · intro ht
    obtain ⟨o, ho, he⟩ := List.mem_map.mp ht
    exact ⟨o, ho, he⟩

#print axioms ascending_cons
#print axioms ins_self
#print axioms mem_ins
#print axioms ascending_ins
#print axioms mem_canon
#print axioms ascending_canon
#print axioms ascending_ext
#print axioms canon_of_ascending
#print axioms canon_idem
#print axioms dupProg_wf
#print axioms dup_sol_one
#print axioms dup_sol_two
#print axioms synthE_is_a_solution

/-! ## §A — BREAK 1. The two readings do NOT exhaust the design space

The target's headline is "REFUTED, on both readings", and its §7 rests the
verdict on the hypothesis that "every candidate `SynthAER` falls in one of the
two classes". A third class exists, and the packet has already built it:
`T017.lean:668` declares

```text
def SynthAER (r : RawProgram) (a : AER) : Prop :=
  a.A = r.resultTy ∧ SynthRow r opsErr Block.handles a.E ∧ ...
```

with `T017.lean:596 SynthRow r own kill row := ∃ s, Least r own kill s ∧ row =
(tagUniverse r own).filter ...` — a `Prop`-valued relation that is explicitly
NOT the graph of the computed `synthRow`, whose single-valuedness
(`T017.lean:621 synthRow_unique`) is proved by antisymmetry of leastness
composed with canonical spelling.

At the target's own carrier that class is `SynthEc`: the synthesis judgment
CARRYING its canonical-spelling side condition, rather than the bare
membership judgment `SynthE`. This is not the target's §6 "repair" under a new
name — §6 states a uniqueness theorem ABOUT a modified predicate, and then
still reports the row as refuted. §A states the DAG's row itself, unmodified,
at the third candidate meaning, and it is TRUE. -/

def SynthEc (r : RawProgram) (e : List Tag) : Prop := Ascending e ∧ SynthE r e

/-- **`EC1-T016` AS WRITTEN, at the third reading: TRUE.** Same quantifier
shape as `PROOF-DAG.md:218`, same premise, `SynthAER` instantiated to the
canonically-spelled synthesis judgment. Nothing is weakened. -/
theorem A1_T016_is_TRUE_at_the_third_reading :
    ∀ r : RawProgram, ProgramWF r → ExistsUnique' (SynthEc r) := by
  intro r _
  refine ⟨synthE r, ⟨ascending_canon _, synthE_is_a_solution r⟩, ?_⟩
  rintro y ⟨hay, hsy⟩
  exact ascending_ext hay (ascending_canon _)
    (fun t => (hsy t).symm.trans (synthE_is_a_solution r t))

/-- The third reading is genuinely distinct from reading B: it is a STRICTLY
stronger judgment, so it is not `SynthE` renamed. -/
theorem A2_third_reading_is_not_reading_B : ¬ ∀ r e, SynthEc r e ↔ SynthE r e := by
  intro h
  have hasc : Ascending [7, 7] := ((h dupProg [7, 7]).mpr dup_sol_two).1
  rw [ascending_cons] at hasc
  exact Nat.lt_irrefl 7 (hasc.1 7 (by simp))

/-- Nor is it reading A: the specification REFUSES rows, so it is not satisfied
by every candidate the way a function graph is. This is `T017.lean:952
SynthAER_refuses_the_empty_row` at this carrier. -/
theorem A3_third_reading_refuses_the_empty_row : ¬ SynthEc dupProg [] := by
  rintro ⟨_, hs⟩
  have h7 := (hs 7).mp ⟨⟨7⟩, by simp [dupProg], rfl⟩
  simp at h7

/-- And it refuses an over-approximating row, so coverage alone does not
satisfy it. -/
theorem A4_third_reading_refuses_over_approximation : ¬ SynthEc dupProg [7, 9] := by
  rintro ⟨_, hs⟩
  obtain ⟨o, ho, hto⟩ := (hs 9).mpr (by simp)
  simp [dupProg] at ho
  subst ho
  simp at hto

/-- The guard is what carries uniqueness — dropping it returns reading B, which
IS false. So the third reading is not a relabelling of reading A either: its
uniqueness is `ascending_ext`, and deleting the conjunct destroys it. -/
theorem A5_the_guard_is_load_bearing :
    (∀ r : RawProgram, ProgramWF r → ExistsUnique' (SynthEc r))
    ∧ ¬ ∀ r : RawProgram, ProgramWF r → ExistsUnique' (SynthE r) := by
  refine ⟨A1_T016_is_TRUE_at_the_third_reading, ?_⟩
  intro h
  obtain ⟨x, _, huniq⟩ := h dupProg dupProg_wf
  have h1 : [7] = x := huniq [7] dup_sol_one
  have h2 : [7, 7] = x := huniq [7, 7] dup_sol_two
  exact absurd (h1.trans h2.symm) (by decide)

/-- **The exhaustiveness claim, refuted in one statement.** There is a
`SynthAER` candidate that is neither satisfied-by-any-row (reading A's defect)
nor multi-valued (reading B's defect). The trichotomy the verdict rests on has
a third cell, and it is occupied. -/
theorem A6_exhaustiveness_claim_is_false :
    ∃ S : RawProgram → List Tag → Prop,
      (∀ r, ProgramWF r → ExistsUnique' (S r))
      ∧ (∃ r e, ¬ S r e) :=
  ⟨SynthEc, A1_T016_is_TRUE_at_the_third_reading, dupProg, [], A3_third_reading_refuses_the_empty_row⟩

#print axioms A1_T016_is_TRUE_at_the_third_reading
#print axioms A2_third_reading_is_not_reading_B
#print axioms A3_third_reading_refuses_the_empty_row
#print axioms A4_third_reading_refuses_over_approximation
#print axioms A5_the_guard_is_load_bearing
#print axioms A6_exhaustiveness_claim_is_false

/-! ## §B — BREAK 2. Refutation is ANTI-monotone in the premise

The target's assumption block says its two-clause `ProgramWF` "is therefore
WEAKER than the packet's, which STRENGTHENS the refutation". That is backwards.
`¬ ∀ r, P r → C r` needs a witness satisfying `P`; if the real premise `P⁺` is
stronger, the witness need not satisfy it, and the refutation does not carry.

This is not a pedantic point about the direction of an arrow. §B exhibits an
INHABITED, non-degenerate strengthening of the target's own `ProgramWF` under
which the reading-B row is TRUE — so the ten unmodelled clauses are not a free
margin of safety for Result 2, they are an open obligation. -/

def emptyProg : RawProgram := { ops := [], declaredE := [] }

/-- A strengthening of the target's `ProgramWF` by one extra clause. It is not
`False` in disguise: §B2 inhabits it. -/
def ProgramWFplus (r : RawProgram) : Prop := ProgramWF r ∧ r.ops = []

theorem B1_plus_is_a_strengthening (r : RawProgram) (h : ProgramWFplus r) :
    ProgramWF r := h.1

theorem B2_plus_is_inhabited : ProgramWFplus emptyProg :=
  ⟨⟨by simp [RowsWF, emptyProg], rfl⟩, rfl⟩

/-- **Reading B's row is TRUE under the strengthening.** Same statement the
target refutes, same `SynthE`, premise strengthened by one clause. -/
theorem B3_readingB_is_TRUE_under_the_strengthening :
    ∀ r : RawProgram, ProgramWFplus r → ExistsUnique' (SynthE r) := by
  intro r h
  have hno : ∀ t, ¬ Contributes r t := by
    rintro t ⟨o, ho, _⟩
    rw [h.2] at ho
    exact absurd ho (by simp)
  have hnil : ∀ e, SynthE r e → e = [] := by
    intro e he
    have hmem : ∀ t, t ∉ e := fun t ht => hno t ((he t).mpr ht)
    cases e with
    | nil => rfl
    | cons a as => exact absurd (show a ∈ a :: as by simp) (hmem a)
  exact ⟨[], fun t => ⟨fun hc => absurd hc (hno t), fun ht => absurd ht (by simp)⟩, hnil⟩

/-- **The transfer argument, refuted.** All three conjuncts hold at once: the
row is refuted at the target's `ProgramWF`, it HOLDS at a strengthening, and
the strengthening entails the target's `ProgramWF`. So "weaker premise
strengthens the refutation" is false as a rule, and Result 2's transfer to the
packet's twelve-clause `ProgramWF` is an assumption about the ten unmodelled
clauses, not a consequence of what is proved. -/
theorem B4_refutation_does_not_transfer_along_strengthening :
    (¬ ∀ r : RawProgram, ProgramWF r → ExistsUnique' (SynthE r))
    ∧ (∀ r : RawProgram, ProgramWFplus r → ExistsUnique' (SynthE r))
    ∧ (∀ r : RawProgram, ProgramWFplus r → ProgramWF r) :=
  ⟨A5_the_guard_is_load_bearing.2, B3_readingB_is_TRUE_under_the_strengthening,
    B1_plus_is_a_strengthening⟩

/-- By contrast, reading A's tautology result IS monotone, because the target
quantified it over an arbitrary premise predicate. Recorded so the two results
are not tarred with one brush: Result 1 survives §B intact, Result 2 does
not. -/
theorem B5_readingA_result_is_premise_monotone
    (P : RawProgram → Prop) (g : RawProgram → List Tag) (r : RawProgram) (_ : P r) :
    ExistsUnique' (fun e => g r = e) :=
  ⟨g r, rfl, fun _ h => h.symm⟩

#print axioms B1_plus_is_a_strengthening
#print axioms B2_plus_is_inhabited
#print axioms B3_readingB_is_TRUE_under_the_strengthening
#print axioms B4_refutation_does_not_transfer_along_strengthening
#print axioms B5_readingA_result_is_premise_monotone

/-! ## §C — BREAK 3. `AERWF` normalizes the wrong side

`ALGEBRA.md:316` clause 11, verbatim: "`AERWF`: synthesized `A/E/R` normalizes
to the declared triple". The subject of "normalizes" is the SYNTHESIZED triple
and the target of "to" is the DECLARED one, i.e. `canon (synth) = declared`.
The target models it as `canon (declared) = synth` — normalization on the other
operand — and its §2 docstring defends that choice as "not silently assuming
the declared row is canonical".

The choice is not neutral. `synthE` is already canonical, so the literal
reading collapses to plain equality, and everything Result 5 rests on inverts:
`RowsWF` becomes DERIVABLE rather than independently necessary, the target's
`declPerm` witness stops being a counterexample, and `aer_synthesis_agrees`
becomes a restatement of its own hypothesis — the exact defect the target
convicts `EC1-T016` of. -/

/-- The literal reading of `ALGEBRA.md:316`. -/
def AERWFlit (r : RawProgram) : Prop := canon (synthE r) = r.declaredE

theorem C1_synthE_is_already_canonical (r : RawProgram) : canon (synthE r) = synthE r :=
  canon_of_ascending (ascending_canon _)

/-- Under the literal reading clause 11 IS the agreement statement. -/
theorem C2_literal_clause11_is_plain_equality (r : RawProgram) :
    AERWFlit r ↔ r.declaredE = synthE r := by
  unfold AERWFlit
  rw [C1_synthE_is_already_canonical]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- **`aer_synthesis_agrees` becomes a restatement of its hypothesis.** No
`RowsWF`, no proof content: the conclusion is the premise, re-oriented. -/
theorem C3_agreement_is_a_restatement_under_literal_clause11
    (r : RawProgram) (h : AERWFlit r) : r.declaredE = synthE r :=
  (C2_literal_clause11_is_plain_equality r).mp h

/-- **`RowsWF` stops being independent.** Clause 3's canonicality half is
DERIVABLE from the literal clause 11, so the target's claim that both conjuncts
are separately necessary holds only for its own side-choice. -/
theorem C4_RowsWF_is_derivable_under_literal_clause11
    (r : RawProgram) (h : AERWFlit r) : RowsWF r := by
  rw [RowsWF, C3_agreement_is_a_restatement_under_literal_clause11 r h]
  exact ascending_canon _

/-- **The target's `agreement_needs_RowsWF` witness is disarmed.** `declPerm`
satisfies the target's `AERWF` but NOT the literal one, so it does not witness
anything against the literal clause 11. The two spellings of clause 11 are
genuinely different propositions, and the packet has never chosen between
them. -/
theorem C5_the_two_spellings_of_clause_11_differ :
    AERWF declPerm ∧ ¬ AERWFlit declPerm := by
  refine ⟨rfl, ?_⟩
  intro h
  have h2 : synthE declPerm = declPerm.declaredE :=
    (C1_synthE_is_already_canonical declPerm).symm.trans h
  exact absurd h2 (by decide)

/-- Put together: under the literal reading, the whole of Result 5 has no live
premise either. The target's verdict that `aer_synthesis_agrees` is "where the
premise is LIVE" is contingent on a modelling decision that departs from the
line it cites. -/
theorem C6_result5_liveness_is_side_choice_dependent :
    (∀ r : RawProgram, AERWFlit r → RowsWF r)
    ∧ (∀ r : RawProgram, AERWFlit r → r.declaredE = synthE r) :=
  ⟨C4_RowsWF_is_derivable_under_literal_clause11,
    C3_agreement_is_a_restatement_under_literal_clause11⟩

#print axioms C1_synthE_is_already_canonical
#print axioms C2_literal_clause11_is_plain_equality
#print axioms C3_agreement_is_a_restatement_under_literal_clause11
#print axioms C4_RowsWF_is_derivable_under_literal_clause11
#print axioms C5_the_two_spellings_of_clause_11_differ
#print axioms C6_result5_liveness_is_side_choice_dependent


/-! ## §D — BREAK 4. `ProgramWF` IS the agreement, so Result 5's premise is not "live"

The target's Result 5 headline calls `aer_synthesis_agrees : ProgramWF r ->
r.declaredE = synthE r` "THE NEAREST TRUE STATEMENT WITH A LIVE PREMISE" and
"`AERWF` becoming DERIVABLE, which is content", contrasting it with §3 and §6
where the premise is discarded.

At the target's OWN spelling the premise and the conclusion are EQUIVALENT.
Nothing becomes derivable: the two-clause conjunction is re-spelled as one
equation, and the converse holds too. That is a useful normalization result,
but it is not a live premise in the sense the report claims — the hypothesis is
interchangeable with the thing it is said to buy. -/

theorem D1_ProgramWF_is_exactly_the_agreement (r : RawProgram) :
    ProgramWF r ↔ r.declaredE = synthE r := by
  constructor
  · intro h
    exact (canon_of_ascending h.1).symm.trans h.2
  · intro h
    refine ⟨?_, ?_⟩
    · show Ascending r.declaredE
      rw [h]
      exact ascending_canon _
    · show canon r.declaredE = synthE r
      rw [h]
      exact canon_of_ascending (ascending_canon _)

/-- **Result 5's converse holds.** So `aer_synthesis_agrees` is the forward half
of a biconditional, not a derivation of new content from a working hypothesis. -/
theorem D2_the_converse_holds (r : RawProgram) (h : r.declaredE = synthE r) :
    ProgramWF r := (D1_ProgramWF_is_exactly_the_agreement r).mpr h

/-- And the literal clause 11 of §C is, on its own, the whole two-clause
`ProgramWF`. Clause 3's canonicality half is redundant under the reading
`ALGEBRA.md:316` actually states — which is why §C's `RowsWF`-necessity
counterexample evaporates there. -/
theorem D3_literal_clause11_alone_is_ProgramWF (r : RawProgram) :
    AERWFlit r ↔ ProgramWF r :=
  Iff.trans (C2_literal_clause11_is_plain_equality r)
    (D1_ProgramWF_is_exactly_the_agreement r).symm

#print axioms D1_ProgramWF_is_exactly_the_agreement
#print axioms D2_the_converse_holds
#print axioms D3_literal_clause11_alone_is_ProgramWF

/-! ## §F — the falsifier battery

Every falsifier that touches this row, exercised at the target's carrier.
`EC1-F02`, `EC1-F04`-`EC1-F08` need a `Resume`/handler/resource/host carrier
that neither the target nor this file builds; they are recorded as NOT RUN in
the report rather than silently skipped. -/

/-- **`EC1-F01` — delete a target block.** Removing a contributing operation
breaks `AERWF`: the declared row is now an over-claim. `ProgramWF` is not
preserved under deletion, so `aer_synthesis_agrees` cannot be used across an
edit without re-checking. -/
def permProg_minus : RawProgram := { ops := [⟨7⟩], declaredE := [7, 9] }

theorem F01_deletion_breaks_ProgramWF : ¬ ProgramWF permProg_minus := by
  rintro ⟨_, h2⟩
  have h3 : canon permProg_minus.declaredE = synthE permProg_minus := h2
  exact absurd h3 (by decide)

/-- **`EC1-F03` — duplicate an operation ID.** Two operations raising one tag.
`ProgramWF` still HOLDS (the synthesizer dedups), and the reading-B refutation
survives, so the target's Result 2 is not an artifact of a one-operation
program. -/
def dupOps : RawProgram := { ops := [⟨7⟩, ⟨7⟩], declaredE := [7] }

theorem F03_duplicate_ops_still_ProgramWF : ProgramWF dupOps :=
  ⟨by simp [RowsWF, dupOps], rfl⟩

theorem F03_refutation_survives_duplicate_ops :
    ¬ ∀ r : RawProgram, ProgramWF r → ExistsUnique' (SynthE r) := by
  intro h
  obtain ⟨x, _, huniq⟩ := h dupOps F03_duplicate_ops_still_ProgramWF
  have s1 : SynthE dupOps [7] := by
    intro t
    constructor
    · rintro ⟨o, ho, rfl⟩; simp [dupOps] at ho; simp [ho]
    · intro ht; simp at ht; exact ⟨⟨7⟩, by simp [dupOps], by simp [ht]⟩
  have s2 : SynthE dupOps [7, 7] := by
    intro t
    constructor
    · rintro ⟨o, ho, rfl⟩; simp [dupOps] at ho; simp [ho]
    · intro ht; simp at ht; exact ⟨⟨7⟩, by simp [dupOps], by simp [ht]⟩
  exact absurd ((huniq [7] s1).trans (huniq [7, 7] s2).symm) (by decide)

/-- **`EC1-F09` — claim too small an `E`.** The target's own `declShort`. -/
def declShort : RawProgram := { ops := [⟨7⟩], declaredE := [] }

theorem F09_under_claiming_E_is_rejected : ¬ ProgramWF declShort := by
  rintro ⟨_, h2⟩
  have h3 : canon declShort.declaredE = synthE declShort := h2
  exact absurd h3 (by decide)

/-- **`EC1-F09`, the other direction — claim too LARGE an `E`.** The target
never tests over-claiming; `ALGEBRA.md:123` says "exactly", so it must be
rejected, and it is. -/
def declLarge : RawProgram := { ops := [⟨7⟩], declaredE := [7, 9] }

theorem F09_over_claiming_E_is_rejected : ¬ ProgramWF declLarge := by
  rintro ⟨_, h2⟩
  have h3 : canon declLarge.declaredE = synthE declLarge := h2
  exact absurd h3 (by decide)

/-- **`EC1-F10` — normalize an already normalized graph.** Idempotent, and on a
well-formed program renormalizing the declared row is the identity. -/
theorem F10_renormalizing_a_wf_program_is_identity
    (r : RawProgram) (h : ProgramWF r) : canon r.declaredE = r.declaredE :=
  canon_of_ascending h.1

/-- `EC1-F10`, sharper: canonicalizing the declared row REPAIRS clause 3 while
preserving clause 11. So the target's `declPerm` witness for
`agreement_needs_RowsWF` is a normalization defect that `EC1-D026`-style
normalization removes — further evidence that clause 3's necessity is an
artifact of where `canon` was placed (§C), not a semantic obligation. -/
theorem F10_canonicalizing_repairs_RowsWF_preserving_AERWF
    (r : RawProgram) (h : AERWF r) :
    ProgramWF { r with declaredE := canon r.declaredE } := by
  refine ⟨ascending_canon _, ?_⟩
  show canon (canon r.declaredE) = synthE { r with declaredE := canon r.declaredE }
  rw [canon_idem]
  exact h

/-- **`EC1-F81` — one raw program, two independent defects.** Both modelled
clauses fail at once. The target builds no checker, so which diagnostic is
reported LATER is not answerable in its carrier; that is recorded as an
observational gap rather than a pass. -/
def twoDefects : RawProgram := { ops := [⟨7⟩, ⟨9⟩], declaredE := [9, 9] }

theorem F81_both_clauses_fail_together :
    ¬ RowsWF twoDefects ∧ ¬ AERWF twoDefects := by
  constructor
  · intro h
    rw [RowsWF, twoDefects, ascending_cons] at h
    exact Nat.lt_irrefl 9 (h.1 9 (by simp))
  · intro h
    have h3 : canon twoDefects.declaredE = synthE twoDefects := h
    exact absurd h3 (by decide)

#print axioms F01_deletion_breaks_ProgramWF
#print axioms F03_duplicate_ops_still_ProgramWF
#print axioms F03_refutation_survives_duplicate_ops
#print axioms F09_under_claiming_E_is_rejected
#print axioms F09_over_claiming_E_is_rejected
#print axioms F10_renormalizing_a_wf_program_is_identity
#print axioms F10_canonicalizing_repairs_RowsWF_preserving_AERWF
#print axioms F81_both_clauses_fail_together

end AttackT016
