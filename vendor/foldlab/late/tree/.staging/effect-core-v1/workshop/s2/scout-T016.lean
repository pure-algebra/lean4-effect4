import Cas.IR.Reach
import Cas.Backend.Canon

/-!
# Effect Core v1 — scout probe for `EC1-T016` (`aer_synthesis_unique`)

Slice `EC1-S2`, the admission boundary. SCOUT ARTEFACT ONLY: nothing here is
proposed for `library/` or for `formal/effect-core-v1/`. It settles the row

```text
EC1-T016  aer_synthesis_unique : ProgramWF r -> exists! aer, SynthAER r aer
```

Run it from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/scout-T016.lean
```

`SynthAER` has **no** `PROPOSED TERM` row anywhere in `PROOF-DAG.md` §2. It
occurs only inside the `EC1-T016` and `EC1-T017` signatures. So this file does
not prove things about "the" `SynthAER`; it enumerates the three readings the
packet's own text can supply and settles each one.

| § | Reading of `SynthAER` | Verdict |
|---|---|---|
| 1 | function graph, or `ALGEBRA.md` §4.3 clause 11 `AERWF` | **VACUOUS** — and the premise is provably dead |
| 2 | coverage/closure judgment over a row carrier | **FALSE** — uniqueness fails by spelling |
| 3 | closure + minimality, still on a raw list carrier | **FALSE** — minimality does not fix a representative |
| 4 | closure + minimality + canonical spelling | **TRUE**, and a real proof |
| 5 | decidability of the synthesis fixpoint | the estate's bound is unavailable once a back edge is legal |
| 6 | exactness | minimality *is* the exactness content; coverage alone is a MAY over-approximation |

No `sorry`, no `axiom`, no `native_decide`, no `#eval` for a claim.
`#print axioms` receipts at the foot.

Standing law respected: nothing here mints a second `Sig`, `Prog`, `PProg`,
`Refusal`, or CAS spelling. The row carrier of §2–§4 is `List Nat`, a scratch
stand-in used only to exhibit the spelling hazard; the estate's real carrier
and its canonical-spelling theorems are `Cas/Backend/Canon.lean`, referenced
in §4 rather than duplicated.
-/

namespace ScoutT016

/-- `∃!` does not parse in this toolchain (`library/cas` carries no Mathlib),
so the packet's `exists!` rows are spelled by hand. Same spelling as
`workshop/s2/scout-T011.lean` so the two probes compare directly. -/
def ExistsUnique' {α : Sort u} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ ∀ y, p y → y = x

/-! ## §1 — the `AERWF` reading: `EC1-T016` is entailed by one clause of its
own premise, and the premise is dead

`ALGEBRA.md` §4.3 clause 11 reads: *"`AERWF`: synthesized `A/E/R` normalizes to
the declared triple"*. Two facts about that sentence decide the row.

First, `declaredAER` is a **field of `RawProgram`** (`ALGEBRA.md` §4.1). So the
`aer` that `EC1-T016` asks to exist is already carried by `r`; it is recovered
by projection, and the synthesizer is never called.

Second, `AERWF` is a conjunct of `ProgramWF`, which is `EC1-T016`'s own
premise. The row therefore asks for something its hypothesis already supplies.

Both are proved below of an ARBITRARY `norm` and `synth`, so the result
transfers the moment `RawProgram` has a `declaredAER` field and clause 11 has
that shape — and no sooner. -/

namespace Declared

variable {AER : Type}

/-- The raw carrier, cut down to the one field that decides the question.
`rest` stands for the eight tables `ALGEBRA.md` §4.1 lists; nothing below
inspects it. -/
structure Raw (AER : Type) where
  /-- `ALGEBRA.md` §4.1 `declaredAER` — the *claimed* result/error/requirements. -/
  declared : AER
  /-- everything else in the raw program. -/
  rest : Nat

variable (norm : AER → AER) (synth : Raw AER → AER)

/-- `ALGEBRA.md` §4.3 clause 11, verbatim: the synthesized triple normalizes to
the declared one. -/
def AERWF (r : Raw AER) : Prop := norm (synth r) = norm r.declared

/-- The only `SynthAER` the D-list can supply once `synth` is a function: its
graph, post-normalization. -/
def SynthAER (r : Raw AER) (a : AER) : Prop := a = norm (synth r)

/-- **`EC1-T016` holds with `True` in place of `ProgramWF`.** The premise is
not weakened here — it is *deleted*, and the row still goes through. This is
the §3 vacuity pattern of the local-anchor report (`T003`/`T008`/`T035`/`T115`)
at the admission boundary. -/
theorem premise_is_dead (r : Raw AER) :
    ExistsUnique' (SynthAER norm synth r) :=
  ⟨norm (synth r), rfl, fun _ h => h⟩

/-- Sharper, and specific to `T016`: under clause 11 the unique `aer` is the
NORMALIZED DECLARED FIELD — computed from `r` by projection. `synth` appears in
neither the statement nor the witness. A checker that never synthesizes
anything satisfies `EC1-T016`. -/
theorem witness_is_the_declared_field (r : Raw AER) (h : AERWF norm synth r) :
    ExistsUnique' (SynthAER norm synth r)
      ∧ SynthAER norm synth r (norm r.declared) :=
  ⟨premise_is_dead norm synth r, h.symm⟩

/-- And therefore the row is entailed by ONE conjunct of its own premise.
Stated as an implication so the entailment is visible: clause 11 alone gives
the whole conclusion, so the other eleven clauses of `ProgramWF` are unused. -/
theorem clause_eleven_entails_T016 (r : Raw AER) :
    AERWF norm synth r →
      ExistsUnique' (SynthAER norm synth r) :=
  fun _ => premise_is_dead norm synth r

end Declared

/-! ## §2 — the coverage reading: uniqueness is FALSE, not vacuous

The only reading under which `EC1-T016` is not a tautology makes `SynthAER` a
genuine RELATION: a *coverage* judgment, closing the reachable operations'
`errorRow`/`requirementRow` contributions over the block graph. `ALGEBRA.md`
§2.1 demands `E` contain "exactly the typed failure alternatives that may
escape" — a least closure.

Under that reading uniqueness is not free; it is **false**, because a coverage
judgment constrains a row's MEMBERS and a row is a keyed LIST. This is
`EC1-CE030` (`rowEq r s -> norm r = norm s` is false for arbitrary keyed rows)
and `R16`'s second half arriving at the AER carrier.

`Tag` stands for the operation-derived contribution; `Row` for `ErrorRow` /
`RequirementRow`. Both are scratch stand-ins. -/

namespace Coverage

abbrev Tag := Nat
abbrev Row := List Tag

/-- The coverage judgment: every contribution reachable in `r` is in `a`.
This is `SynthAER` read as a relation rather than a function graph. -/
def Covers (contribs : Row) (a : Row) : Prop := ∀ t ∈ contribs, t ∈ a

/-- Duplication satisfies coverage. -/
theorem covers_dup : Covers [0] [0, 0] := by
  intro t ht
  simp at ht
  simp [ht]

/-- So does the singleton. -/
theorem covers_single : Covers [0] [0] := by
  intro t ht; exact ht

/-- Two spellings of the same content, both admitted. -/
theorem two_spellings : ([0] : Row) ≠ [0, 0] := by decide

/-- **`EC1-T016` is FALSE under the coverage reading.** No uniqueness, for a
single-contribution program — the smallest possible witness. -/
theorem coverage_synthesis_is_not_unique :
    ¬ ExistsUnique' (Covers [0]) := by
  rintro ⟨a, _, huniq⟩
  have h1 : ([0] : Row) = a := huniq [0] covers_single
  have h2 : ([0, 0] : Row) = a := huniq [0, 0] covers_dup
  exact two_spellings (h1.trans h2.symm)

/-- Permutation is the second, independent way it fails — the exact shape of
`EC1-CE030`'s witness. Kept separate because a `Nodup` premise kills the
duplication route above but not this one. -/
theorem covers_ab : Covers [0, 1] [0, 1] := by intro t ht; exact ht

theorem covers_ba : Covers [0, 1] [1, 0] := by
  intro t ht
  simp at ht
  rcases ht with h | h <;> simp [h]

theorem coverage_not_unique_by_permutation :
    ¬ ExistsUnique' (Covers [0, 1]) := by
  rintro ⟨a, _, huniq⟩
  have h1 : ([0, 1] : Row) = a := huniq [0, 1] covers_ab
  have h2 : ([1, 0] : Row) = a := huniq [1, 0] covers_ba
  have : ([0, 1] : Row) = [1, 0] := h1.trans h2.symm
  exact absurd this (by decide)

/-! ## §3 — minimality alone does not repair it

The obvious patch is to demand the LEAST closure. It is necessary (§6) and it
is not sufficient: minimality is a statement about MEMBERS, and two lists with
the same members are still two lists. `[0]` and `[0,0]` are both
member-minimal. -/

/-- Minimal coverage: covers, and is contained (member-wise) in every cover. -/
def MinCovers (contribs : Row) (a : Row) : Prop :=
  Covers contribs a ∧ ∀ b, Covers contribs b → ∀ t ∈ a, t ∈ b

theorem minCovers_single : MinCovers [0] [0] :=
  ⟨covers_single, fun _ hb t ht => hb t ht⟩

theorem minCovers_dup : MinCovers [0] [0, 0] := by
  refine ⟨covers_dup, fun b hb t ht => ?_⟩
  have h0 : t = 0 := by simpa using ht
  subst h0
  exact hb 0 (by simp)

/-- **Minimality is not enough.** `EC1-T016` is still false after the least-
closure patch, for the same one-contribution program. -/
theorem minimality_does_not_repair :
    ¬ ExistsUnique' (MinCovers [0]) := by
  rintro ⟨a, _, huniq⟩
  have h1 : ([0] : Row) = a := huniq [0] minCovers_single
  have h2 : ([0, 0] : Row) = a := huniq [0, 0] minCovers_dup
  exact two_spellings (h1.trans h2.symm)

/-! ## §4 — the repair: canonical spelling

What restores uniqueness is a CANONICAL SPELLING predicate on the row, not a
stronger closure condition. This is the estate's own move, at its own carrier:

* `Cas/Backend/Canon.lean:484` `eq_of_isCanonServices_of_perm` — two
  guard-passing spellings of one key-`Nodup` service set are the SAME LIST;
* `Cas/Backend/Canon.lean:392` `nodup_keys_of_isCanonServices` — the guard
  supplies the `Nodup` premise `EC1-CE030` proved necessary;
* `Cas/Backend/Canon.lean:402` `canonServices_of_isCanonServices` — a
  guard-passing list is already its own canonical spelling.

The theorem below is that shape re-proved at the scratch row carrier, with
`Pairwise (· < ·)` standing in for the estate's sorted-and-`Nodup` guard. It is
the only theorem in this file whose proof is longer than three lines, which is
the point: the substantive content of `EC1-T016` lives here, and nowhere in the
row as the DAG writes it. -/

/-- Strictly increasing: the scratch canonical-spelling guard. Implies `Nodup`
and fixes the order, exactly as `isCanonServices` does at
`Cas/Backend/Canon.lean`. -/
def IsCanon (a : Row) : Prop := a.Pairwise (· < ·)

theorem not_mem_of_canon_cons {x : Tag} {s : Row} (h : IsCanon (x :: s)) :
    x ∉ s := by
  have hall : ∀ y ∈ s, x < y := (List.pairwise_cons.mp h).1
  intro hx
  exact absurd (hall x hx) (Nat.lt_irrefl x)

theorem canon_tail {x : Tag} {s : Row} (h : IsCanon (x :: s)) : IsCanon s :=
  (List.pairwise_cons.mp h).2

/-- **The uniqueness theorem the row actually owes.** Two canonically spelled
rows with the same members are equal. Everything `EC1-T016` can honestly claim
is a corollary of this plus a least-closure judgment. -/
theorem canon_eq_of_same_members :
    ∀ {a b : Row}, IsCanon a → IsCanon b → (∀ t, t ∈ a ↔ t ∈ b) → a = b := by
  intro a
  induction a with
  | nil =>
    intro b _ _ hm
    cases b with
    | nil => rfl
    | cons y t => exact absurd ((hm y).mpr (by simp)) (by simp)
  | cons x s ih =>
    intro b ha hb hm
    cases b with
    | nil => exact absurd ((hm x).mp (by simp)) (by simp)
    | cons y t =>
      have hxy : x = y := by
        have hx : x = y ∨ x ∈ t := List.mem_cons.mp ((hm x).mp (by simp))
        have hy : y = x ∨ y ∈ s := List.mem_cons.mp ((hm y).mpr (by simp))
        rcases hx with h | hxt
        · exact h
        · rcases hy with h | hys
          · exact h.symm
          · have h1 : x < y := (List.pairwise_cons.mp ha).1 y hys
            have h2 : y < x := (List.pairwise_cons.mp hb).1 x hxt
            exact (Nat.lt_irrefl x (Nat.lt_trans h1 h2)).elim
      subst hxy
      have hxs : x ∉ s := not_mem_of_canon_cons ha
      have hxt : x ∉ t := not_mem_of_canon_cons hb
      have hm' : ∀ u, u ∈ s ↔ u ∈ t := by
        intro u
        constructor
        · intro hu
          rcases List.mem_cons.mp ((hm u).mp (List.mem_cons_of_mem _ hu)) with h | h
          · exact absurd (h ▸ hu) hxs
          · exact h
        · intro hu
          rcases List.mem_cons.mp ((hm u).mpr (List.mem_cons_of_mem _ hu)) with h | h
          · exact absurd (h ▸ hu) hxt
          · exact h
      exact congrArg (fun l => x :: l) (ih (canon_tail ha) (canon_tail hb) hm')

/-- The repaired `EC1-T016`, at the scratch carrier: a least closure that is
also canonically spelled is unique. Note what the statement needs — a canonical
`synth` producing a canonical row, and the canonicity of every RIVAL. Neither
is supplied by `ProgramWF` as `ALGEBRA.md` §4.3 lists it. Clause 3 `RowsWF`
("all rows are canonical and every escaped typed failure is in `E`") reaches
only the rows PRESENT in the raw program — `declaredAER` among them — and the
synthesized triple is not one of them. Read together, clauses 3 and 11 are
already the coverage half and the exactness half of AER synthesis, applied to
the declared triple; that is the second reason `EC1-T016` adds nothing to its
own premise. -/
theorem canonical_min_closure_is_unique
    (contribs : Row) (a : Row) (hca : IsCanon a) (hmin : MinCovers contribs a) :
    ∀ b, IsCanon b → MinCovers contribs b → b = a := by
  intro b hcb hmb
  refine canon_eq_of_same_members hcb hca (fun t => ⟨?_, ?_⟩)
  · intro ht; exact hmb.2 a hmin.1 t ht
  · intro ht; exact hmin.2 b hmb.1 t ht

end Coverage

/-! ## §5 — the decidability of the synthesis fixpoint

`ProgramWF` clause 5 `HandlersWF` quantifies over "every REACHABLE operation",
and any coverage-style `SynthAER` is a fixpoint over the same reachable set. So
clause 11's decidability rests on deciding reachability in the block graph.

The estate decides reachability exactly once, and the module says out loud what
it costs (`Cas/IR/Reach.lean`, verified line by line):

* `:460` `reachIn` — a depth-bounded search, `Bool`-valued;
* `:474` `reachIn_sound` — soundness needs NO admission premise;
* `:494` `reachIn_complete` — completeness consumes `wf w = true`;
* `:401` `reach_index` — the reason: every edge strictly DESCENDS the admission
  index, so a path out of `a` is shorter than `firstIndex w a`;
* `:528` `reachB`, `:541` `reachB_iff`, `:550` `decidableReach` — the decision
  procedure, which the estate deliberately did not register as an `instance`
  because "admission is what makes reachability decidable here".

The asymmetry below is re-derived rather than asserted, so the premise is
visible in the type. -/

namespace Reachability

open Cas

/-- Soundness of the estate's bounded search is premise-free. -/
theorem reach_sound_needs_no_admission {w : Cas.Word} {a b : Cas.Addr32}
    (h : Cas.Word.reachB w a b = true) : Cas.Word.Reach w a b :=
  Cas.Word.reachB_sound h

/-- The decision procedure exists only relative to `wf w`. Re-derived so that
the premise appears in the type of the thing a checker would call. -/
def reach_decided_only_on_admitted {w : Cas.Word} (hw : Cas.Word.wf w = true)
    (a b : Cas.Addr32) : Decidable (Cas.Word.Reach w a b) :=
  Cas.Word.decidableReach hw a b

/-- **What buys the bound, isolated.** `reach_index` is a strictly descending
`Nat` measure along edges. A graph with a two-cycle admits no such measure — so
the estate's completeness argument is unavailable on any graph where a back
edge is legal.

`ALGEBRA.md` §4.2 settles this outright: *"Cycles are ordinary references to
earlier blocks."* `EC1-D028` declares `feedback`, and §5 of the same document
requires only that "loop unfolding consumes at least one transition before
recurring" — a guardedness condition, not acyclicity. The Effect Core block
graph is therefore NOT the estate's DAG, `reach_index` has no analogue there,
and clauses 5 and 11 owe a DIFFERENT bound: a visited-set or cardinality
argument with a pigeonhole completeness proof. The corpus does not contain
one — `Cas/IR/Reach.lean` deliberately took the topological route instead. -/
theorem cycle_admits_no_index_measure {V : Type} {E : V → V → Prop} {a b : V}
    (hab : E a b) (hba : E b a) (mu : V → Nat)
    (hdesc : ∀ x y, E x y → mu y < mu x) : False := by
  have h1 := hdesc a b hab
  have h2 := hdesc b a hba
  omega

/-- The same fact stated positively, so it can be cited as a design
constraint: any strictly descending measure forces acyclicity. -/
theorem index_measure_forces_acyclic {V : Type} {E : V → V → Prop}
    (mu : V → Nat) (hdesc : ∀ x y, E x y → mu y < mu x) (a b : V)
    (hab : E a b) (hba : E b a) : False :=
  cycle_admits_no_index_measure hab hba mu hdesc

end Reachability

/-! ## §6 — exactness: minimality is the whole content, and it is not in the row

`ALGEBRA.md` §2.1 requires `E` to contain "exactly the typed failure
alternatives that may escape" — the LEAST closure, not any closure. A coverage
judgment without minimality is satisfied by every over-approximation, and the
estate has already proved that its own static summary over-approximates:

* `EC1-CE008` (`div4_envelope_does_not_bound_the_error_row`);
* `Cas/Lang/Defun.lean:2131` GAP 1, the suffix after the first refusal (the
  `example` at `:2135`), and `:2143` GAP 2, `put`'s duplicate outcome (the
  `example` at `:2149`) — both verified, and both
  ANONYMOUS `example`s, so they are file-line exhibits and cannot be cited as
  named theorems;
* `Cas/Lang/Fragments.lean:70-78`, which records that `DESIGN.md` §3.1's
  "exact: `over = under = actual`" rung is refuted, and that these two are the
  only two sources of the gap.

`EC1-T017` inherits the same problem: `PROOF-DAG.md` §4 gives it `NO ANCHOR`,
and the nearest object, `PProg.envelope` (`Cas/Lang/Defun.lean:1205`,
verified), is a MAY set.

`EC1-T016` as written contains no minimality conjunct — `exists!` over a
function graph cannot express one. -/

namespace Exactness

open Coverage

/-- Strict over-approximations exist and satisfy coverage. A `SynthAER` stated
as coverage alone therefore admits a checker that reports a too-large `E`,
which is exactly what falsifier `EC1-F09` ("claim too-small `E` or `R`") is the
mirror of. -/
theorem over_approximation_is_admitted :
    Covers [0] [0, 1] ∧ ¬ MinCovers [0] [0, 1] := by
  refine ⟨fun t ht => by simp at ht; simp [ht], ?_⟩
  rintro ⟨_, hmin⟩
  have : (1 : Nat) ∈ ([0] : Row) := hmin [0] covers_single 1 (by simp)
  exact absurd this (by decide)

end Exactness

/-! ## Receipts -/

#print axioms ScoutT016.Declared.premise_is_dead
#print axioms ScoutT016.Declared.witness_is_the_declared_field
#print axioms ScoutT016.Declared.clause_eleven_entails_T016
#print axioms ScoutT016.Coverage.coverage_synthesis_is_not_unique
#print axioms ScoutT016.Coverage.coverage_not_unique_by_permutation
#print axioms ScoutT016.Coverage.minimality_does_not_repair
#print axioms ScoutT016.Coverage.canon_eq_of_same_members
#print axioms ScoutT016.Coverage.canonical_min_closure_is_unique
#print axioms ScoutT016.Reachability.reach_sound_needs_no_admission
#print axioms ScoutT016.Reachability.reach_decided_only_on_admitted
#print axioms ScoutT016.Reachability.cycle_admits_no_index_measure
#print axioms ScoutT016.Exactness.over_approximation_is_admitted

end ScoutT016
