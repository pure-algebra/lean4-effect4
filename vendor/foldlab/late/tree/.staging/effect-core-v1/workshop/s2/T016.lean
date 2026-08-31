import Cas.Backend.Canon

/-!
# `EC1-T016` — `aer_synthesis_unique`

Slice `EC1-S2`, the admission boundary. One row:

```text
EC1-T016  aer_synthesis_unique : ProgramWF r -> exists! aer, SynthAER r aer
```

Run it:

```
cd /Users/pooks/Dev/foldlab/library/cas && \
  lake env lean ../../.staging/effect-core-v1/workshop/s2/T016.lean
```

## Verdict — REFUTED, on both readings, and the two refutations differ

`SynthAER` has no declaration anywhere in the packet. It occurs only inside the
`EC1-T016` and `EC1-T017` rows of `PROOF-DAG.md`; §2 of that file declares
`RawProgram` (D020) through the flow operations (D027-D028) and has no
`PROPOSED TERM` node for it. So the row has no fixed meaning, and both readings
its own documents supply must be settled separately.

* **Reading A — `SynthAER` is the graph of a computed `synthAER`.** This is the
  reading `ALGEBRA.md:316` clause 11 forces ("synthesized `A/E/R` normalizes to
  the declared triple", against a `declaredAER` that `ALGEBRA.md:229` makes a
  FIELD of the raw carrier), and it is the reading every sibling carrier in
  this directory actually built. Under it the row is a **tautology**: §3 proves
  the conclusion with the `ProgramWF` premise DELETED, then for an ARBITRARY
  premise predicate, then for an ARBITRARY synthesizer — including one that
  ignores its input. The row constrains no checker.
* **Reading B — `SynthAER` is a genuine synthesis relation.** This is the
  reading the DAG's own vacuity warning demands, and the only one that could
  rescue the row from §3. Under it the row is **FALSE**: §4 exhibits a
  `ProgramWF` program with two distinct solutions, twice — once by duplication,
  once by permutation. Demanding the LEAST closure does not repair it (§5).

The failure is not an artifact of a toy encoding. It is `EC1-CE030`
(`VERIFIED-KERNEL` — "a permutation with duplicate keys selects different last
values") arriving at the AER carrier. An `ErrorRow` is a keyed LIST;
`library/cas` requires only `cas`, its manifest lists no package, and there is
no Mathlib and no `Finset` in scope. A membership-level synthesis judgment
cannot see the difference between two spellings of one set, and there is no
set-shaped `AER` to escape into.

## What is true instead

* §6 `T016_canonical_unique` — uniqueness is recovered by a CANONICAL-SPELLING
  predicate, not by a stronger closure condition. This is
  `Cas/Backend/Canon.lean:484 eq_of_isCanonServices_of_perm` at the AER
  carrier: of all the spellings of one set, the guard admits exactly one.
  Reported honestly: this row STILL does not use `ProgramWF`.
* §7 `aer_synthesis_agrees : ProgramWF r -> r.declaredE = synthE r` — the
  nearest true statement whose premise is LIVE. Both modelled `ProgramWF`
  conjuncts are proved independently necessary by concrete witnesses, so unlike
  every statement in §3 and §6, deleting a hypothesis makes it false. This is
  `AERWF` becoming DERIVABLE, which is content, and §7 then derives from it the
  relational index fact `EC1-T017` actually needs.

## Receipts and limits

`#print axioms` follows every theorem. No `sorry`, no `axiom`, no
`native_decide`, no `#eval` standing for a claim.

`Classical.choice` appears in exactly the three §0 receipts. Those are
`library/cas` theorems re-elaborated UNCHANGED; the axiom is inherited from
`Canon.lean`'s `List.mergeSort` family — the same ceiling `EC1-CE030` already
records for this normalizer — and is introduced by nothing authored here. Every
theorem in §1-§7 is at `[propext]` or `[propext, Quot.sound]` or axiom-free.

This file proves the STATED PROPOSITIONS ONLY. It is not model assurance and
not implementation assurance, and it closes no proof-DAG row. The carrier is a
MINIMUM: one error row over `Nat` tags, two of the twelve `ALGEBRA.md` §4.3
clauses. That is enough to settle `EC1-T016` — both refutations are exhibited
on programs the carrier ADMITS, and a vacuity proof quantified over an
arbitrary predicate and an arbitrary synthesizer does not get weaker in a
larger carrier. It is NOT enough to say anything about the other ten clauses,
about `A` or `R`, about `check`, or about any run.
-/

namespace EC1T016

/-! ## §0 — Anchor receipts

Re-elaborated from `library/cas` unchanged, so the citations below are checked
rather than asserted. `eq_of_isCanonServices_of_perm` is the estate's own answer
to exactly the problem §4 exhibits, and §6 is that answer transposed to the AER
carrier. These three are the file's only `Classical.choice` users. -/

/-- `Cas/Backend/Canon.lean:484`. Of all the spellings of one service set, the
authoring guard admits exactly one. -/
theorem anchor_canon_pins_one_spelling
    {xs ys : List Cas.Schema.ServiceRef}
    (hx : Cas.Backend.isCanonServices xs = true)
    (hy : Cas.Backend.isCanonServices ys = true)
    (hperm : xs.Perm ys) : xs = ys :=
  Cas.Backend.eq_of_isCanonServices_of_perm hx hy hperm

/-- `Cas/Backend/Canon.lean:402`. A guard-passing list is already its own
canonical spelling — the shape `canon_of_ascending` takes in §2. -/
theorem anchor_guard_is_canonical
    {xs : List Cas.Schema.ServiceRef}
    (h : Cas.Backend.isCanonServices xs = true) :
    Cas.Backend.canonServices xs = xs :=
  Cas.Backend.canonServices_of_isCanonServices h

/-- `Cas/Backend/Canon.lean:392`. The guard SUPPLIES the duplicate-free premise
`EC1-CE030` forces; it is not assumed. -/
theorem anchor_guard_supplies_nodup
    {xs : List Cas.Schema.ServiceRef}
    (h : Cas.Backend.isCanonServices xs = true) :
    (xs.map (·.key)).Nodup :=
  Cas.Backend.nodup_keys_of_isCanonServices h

#print axioms anchor_canon_pins_one_spelling
#print axioms anchor_guard_is_canonical
#print axioms anchor_guard_supplies_nodup

/-! ## §1 — `exists!`, spelled by hand

`ExistsUnique` is not in scope in this environment (`#check @ExistsUnique` is
`Unknown identifier`; toolchain `leanprover/lean4:v4.33.1`, no Mathlib), so
`∃!` does not parse. `EC1-T004`, `EC1-T008`, `EC1-T016`, `EC1-T050` and
`EC1-T090` are all written in the DAG with a connective the target environment
cannot read; each needs this unfolding or a new dependency. -/

def ExistsUnique' {α : Type} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ ∀ y, p y → y = x

/-! ## §2 — The carrier, minimum for this row

`SynthAER` is undeclared, so the row cannot be typed until someone declares it.
What follows is the minimum that lets both readings be stated and compared. It
follows `ALGEBRA.md:229`, where `declaredAER` is a FIELD of the raw carrier —
itself half of why reading A is a projection. -/

/-- One typed failure alternative. `Nat` because `ErrorRow` needs decidable
equality and a canonical order, and nothing here depends on more. -/
abbrev Tag := Nat

/-- An operation, carrying the one alternative it may raise. -/
structure RawOp where
  tag : Tag
deriving DecidableEq, Repr

/-- `EC1-D020 RawProgram`, cut to the two fields this row is about. -/
structure RawProgram where
  ops : List RawOp
  declaredE : List Tag
deriving DecidableEq, Repr

/-- What the graph contributes to `E`: the static MAY set of `ALGEBRA.md:123`,
"`E` contains exactly the typed failure alternatives that may escape". -/
def Contributes (r : RawProgram) (t : Tag) : Prop := ∃ o ∈ r.ops, o.tag = t

/-! ### Canonical spelling

Ordered insertion with duplicate suppression, and its guard. This is
`canonServices`/`isCanonServices` at the tag carrier; `Ascending` carries the
`Nodup`-and-sorted content of that guard in one predicate. -/

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

/-- **Extensionality for canonical rows.** Two canonically spelled rows with the
same members are the SAME LIST. This is `Canon.lean:484` at the tag carrier, and
it is the one substantive proof in this file — everything §6 recovers, it
recovers from here. -/
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

/-- A canonically spelled row is already its own canonical form —
`Canon.lean:402`'s shape. -/
theorem canon_of_ascending {l : List Tag} (h : Ascending l) : canon l = l :=
  ascending_ext (ascending_canon l) h (fun t => mem_canon t l)

theorem canon_idem (l : List Tag) : canon (canon l) = canon l :=
  canon_of_ascending (ascending_canon l)

/-- The synthesized error row: the canonical union of what the graph raises. -/
def synthE (r : RawProgram) : List Tag := canon (r.ops.map RawOp.tag)

/-! ### Two of the twelve clauses

Named after `ALGEBRA.md` §4.3, and only these two: clause 3's canonicality half
and clause 11. Clauses 1, 2, 4-10 and 12 are NOT modelled, and nothing in this
file says anything about them. -/

/-- Clause 3, first half (`RowsWF`, "all rows are canonical"). -/
def RowsWF (r : RawProgram) : Prop := Ascending r.declaredE

/-- Clause 11 (`AERWF`), in `ALGEBRA.md:316`'s own words: the synthesized row
NORMALIZES to the declared triple. Stated with `canon` on the DECLARED side, so
it does not silently assume the declared row is canonical — that is `RowsWF`'s
job, and §7 shows both are separately needed. -/
def AERWF (r : RawProgram) : Prop := canon r.declaredE = synthE r

def ProgramWF (r : RawProgram) : Prop := RowsWF r ∧ AERWF r

#print axioms ascending_cons
#print axioms ins_self
#print axioms mem_ins
#print axioms ascending_ins
#print axioms mem_canon
#print axioms ascending_canon
#print axioms ascending_ext
#print axioms canon_of_ascending
#print axioms canon_idem

/-! ## §3 — Reading A: `SynthAER` as a function graph. THE ROW IS A TAUTOLOGY.

This is the reading `ALGEBRA.md:316` forces, and the reading every sibling
carrier in `workshop/s2/` built: `T010.lean:699`, `T011.lean:218`,
`T012.lean:511`, `T013.lean:375` and `T014.lean:403` each declare `synthAER` as
a total Lean FUNCTION, and none of the five declares a `Prop`-valued
`SynthAER`. Under that convergence `EC1-T016` is dead in every carrier the
packet has actually built. -/

/-- The general fact. `exists!` over the graph of ANY function is provable from
nothing at all. -/
theorem existsUnique_graph {α β : Type} (f : α → β) (a : α) :
    ExistsUnique' (fun b => f a = b) :=
  ⟨f a, rfl, fun _ h => h.symm⟩

/-- `EC1-T016` under reading A, with its premise DELETED. Not weakened — the
`ProgramWF` hypothesis is absent from the statement. -/
theorem T016_functional_is_premise_free (r : RawProgram) :
    ExistsUnique' (fun e => synthE r = e) :=
  existsUnique_graph synthE r

/-- The precise sense in which the row distinguishes nothing: its premise slot
is a FREE VARIABLE. Any `P` whatsoever — the twelve-clause `ProgramWF`, `True`,
`False`, a predicate about the weather — yields the DAG's row. -/
theorem T016_functional_holds_at_every_premise
    (P : RawProgram → Prop) (r : RawProgram) (_ : P r) :
    ExistsUnique' (fun e => synthE r = e) :=
  existsUnique_graph synthE r

/-- Stronger, and this is the operational reading: `EC1-T016` constrains no
synthesizer. It holds of EVERY candidate `g`, including one that ignores its
input — so a checker that synthesizes nothing at all satisfies the row. -/
theorem T016_constrains_no_synthesizer
    (g : RawProgram → List Tag) (r : RawProgram) (_ : ProgramWF r) :
    ExistsUnique' (fun e => g r = e) :=
  existsUnique_graph g r

/-- Instantiated, to leave no doubt: the input-blind constant synthesizer
satisfies `EC1-T016` at every well-formed program. -/
theorem T016_satisfied_by_the_blind_synthesizer
    (r : RawProgram) (h : ProgramWF r) :
    ExistsUnique' (fun e => (fun _ : RawProgram => ([] : List Tag)) r = e) :=
  T016_constrains_no_synthesizer (fun _ => []) r h

/-- And on a well-formed program the row's witness is recovered by PROJECTION
from the raw carrier's own `declaredE` field, without consulting the graph at
all. `ALGEBRA.md:229` makes `declaredAER` a field; clause 11 then hands the
answer back. -/
theorem T016_witness_is_the_declared_field
    (r : RawProgram) (h : ProgramWF r) :
    ExistsUnique' (fun e => synthE r = e) ∧ synthE r = r.declaredE :=
  ⟨existsUnique_graph synthE r, h.2.symm.trans (canon_of_ascending h.1)⟩

#print axioms existsUnique_graph
#print axioms T016_functional_is_premise_free
#print axioms T016_functional_holds_at_every_premise
#print axioms T016_constrains_no_synthesizer
#print axioms T016_satisfied_by_the_blind_synthesizer
#print axioms T016_witness_is_the_declared_field

/-! ## §4 — Reading B: `SynthAER` as a genuine relation. THE ROW IS FALSE.

The DAG's warning says `exists!` is a tautology "unless `SynthAER` is a genuine
RELATION". Reading B takes that instruction. `SynthE r e` says `e` holds exactly
the alternatives the graph contributes — coverage AND exactness, which is
`ALGEBRA.md:123`'s "exactly ... may escape", i.e. the LEAST closure and not an
over-approximation. It is a relation and not a function graph, because it
constrains `e`'s MEMBERS while an `ErrorRow` is a keyed LIST. -/

def SynthE (r : RawProgram) (e : List Tag) : Prop :=
  ∀ t, Contributes r t ↔ t ∈ e

/-- Duplication witness. One operation raising tag 7; the declared row is `[7]`,
canonical, and clause 11 holds — so `ProgramWF` HOLDS at this program. -/
def dupProg : RawProgram := { ops := [⟨7⟩], declaredE := [7] }

/-- Permutation witness: `EC1-CE030`'s shape at the AER carrier. -/
def permProg : RawProgram := { ops := [⟨7⟩, ⟨9⟩], declaredE := [7, 9] }

theorem dupProg_wf : ProgramWF dupProg := ⟨by simp [RowsWF, dupProg], rfl⟩

theorem permProg_wf : ProgramWF permProg := ⟨by simp [RowsWF, permProg], rfl⟩

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

theorem perm_sol_one : SynthE permProg [7, 9] := by
  intro t
  constructor
  · rintro ⟨o, ho, rfl⟩; simp [permProg] at ho
    rcases ho with h | h <;> simp [h]
  · intro ht; simp at ht
    rcases ht with h | h
    · exact ⟨⟨7⟩, by simp [permProg], by simp [h]⟩
    · exact ⟨⟨9⟩, by simp [permProg], by simp [h]⟩

theorem perm_sol_two : SynthE permProg [9, 7] := by
  intro t
  constructor
  · rintro ⟨o, ho, rfl⟩; simp [permProg] at ho
    rcases ho with h | h <;> simp [h]
  · intro ht; simp at ht
    rcases ht with h | h
    · exact ⟨⟨9⟩, by simp [permProg], by simp [h]⟩
    · exact ⟨⟨7⟩, by simp [permProg], by simp [h]⟩

/-- `SynthE` is a genuine relation, not a function graph: it relates ONE
well-formed program to TWO distinct rows. This is the hypothesis reading B was
supposed to supply, and it is exactly what kills the row. -/
theorem SynthE_is_genuinely_relational :
    ∃ r : RawProgram, ProgramWF r ∧ ∃ e₁ e₂ : List Tag,
      e₁ ≠ e₂ ∧ SynthE r e₁ ∧ SynthE r e₂ :=
  ⟨dupProg, dupProg_wf, [7], [7, 7], by decide, dup_sol_one, dup_sol_two⟩

/-- **`EC1-T016` under reading B is FALSE.** The premise HOLDS at the witness
and the conclusion fails. -/
theorem T016_relational_is_false :
    ¬ ∀ r : RawProgram, ProgramWF r → ExistsUnique' (SynthE r) := by
  intro h
  obtain ⟨x, _, huniq⟩ := h dupProg dupProg_wf
  have h1 : [7] = x := huniq [7] dup_sol_one
  have h2 : [7, 7] = x := huniq [7, 7] dup_sol_two
  exact absurd (h1.trans h2.symm) (by decide)

/-- Again by PERMUTATION rather than duplication, so the failure is not an
artifact of one degenerate spelling. This is `EC1-CE030` landing on the AER
carrier, where the register currently records it only against `EC1-T002`. -/
theorem T016_relational_is_false_by_permutation :
    ¬ ∀ r : RawProgram, ProgramWF r → ExistsUnique' (SynthE r) := by
  intro h
  obtain ⟨x, _, huniq⟩ := h permProg permProg_wf
  have h1 : [7, 9] = x := huniq [7, 9] perm_sol_one
  have h2 : [9, 7] = x := huniq [9, 7] perm_sol_two
  exact absurd (h1.trans h2.symm) (by decide)

#print axioms dupProg_wf
#print axioms permProg_wf
#print axioms dup_sol_one
#print axioms dup_sol_two
#print axioms perm_sol_one
#print axioms perm_sol_two
#print axioms SynthE_is_genuinely_relational
#print axioms T016_relational_is_false
#print axioms T016_relational_is_false_by_permutation

/-! ## §5 — Minimality does not repair it

The obvious patch is to demand the LEAST closure, which `ALGEBRA.md:123`
requires anyway. It does not help: minimality constrains MEMBERS, and the two
witnesses have the same members. -/

/-- `e` is a solution, and every solution contains it. -/
def MinSynthE (r : RawProgram) (e : List Tag) : Prop :=
  SynthE r e ∧ ∀ e', SynthE r e' → ∀ t, t ∈ e → t ∈ e'

theorem T016_minimal_is_still_false :
    ¬ ∀ r : RawProgram, ProgramWF r → ExistsUnique' (MinSynthE r) := by
  intro h
  obtain ⟨x, _, huniq⟩ := h dupProg dupProg_wf
  have m1 : MinSynthE dupProg [7] :=
    ⟨dup_sol_one, fun e' he' t ht => (he' t).mp ((dup_sol_one t).mpr ht)⟩
  have m2 : MinSynthE dupProg [7, 7] :=
    ⟨dup_sol_two, fun e' he' t ht => (he' t).mp ((dup_sol_two t).mpr ht)⟩
  have h1 : [7] = x := huniq [7] m1
  have h2 : [7, 7] = x := huniq [7, 7] m2
  exact absurd (h1.trans h2.symm) (by decide)

#print axioms T016_minimal_is_still_false

/-! ## §6 — The repair: a canonical-spelling predicate

Not a stronger closure condition — a guard on the SPELLING. This is the
estate's own move, receipted at §0: `isCanonServices` admits exactly one
spelling per set (`Canon.lean:484`), and a guard-passing list is already its own
canonical form (`Canon.lean:402`). -/

theorem synthE_is_a_solution (r : RawProgram) : SynthE r (synthE r) := by
  intro t
  rw [synthE, mem_canon]
  constructor
  · rintro ⟨o, ho, rfl⟩; exact List.mem_map.mpr ⟨o, ho, rfl⟩
  · intro ht
    obtain ⟨o, ho, he⟩ := List.mem_map.mp ht
    exact ⟨o, ho, he⟩

/-- **The nearest true uniqueness statement.** `EC1-T016`'s shape survives once
the solution is required to be canonically spelled. Reported honestly: this
holds for EVERY raw program, so the `ProgramWF` premise is still doing no proof
work — see `T016_canonical_at_wf`. What the premise buys is §7. -/
theorem T016_canonical_unique (r : RawProgram) :
    ExistsUnique' (fun e => Ascending e ∧ SynthE r e) := by
  refine ⟨synthE r, ⟨ascending_canon _, synthE_is_a_solution r⟩, ?_⟩
  rintro y ⟨hay, hsy⟩
  exact ascending_ext hay (ascending_canon _)
    (fun t => (hsy t).symm.trans (synthE_is_a_solution r t))

/-- The DAG's row, repaired to reading B plus a canonical guard. The premise is
UNUSED, and that is stated rather than hidden: the proof discards it. -/
theorem T016_canonical_at_wf (r : RawProgram) (_ : ProgramWF r) :
    ExistsUnique' (fun e => Ascending e ∧ SynthE r e) :=
  T016_canonical_unique r

#print axioms synthE_is_a_solution
#print axioms T016_canonical_unique
#print axioms T016_canonical_at_wf

/-! ## §7 — Where the premise is LIVE

`aer_synthesis_agrees` is the statement the `EC1-T010` scout named as T016's
replacement, proved here. It consumes BOTH modelled clauses, and each is shown
independently necessary by a concrete witness — so unlike every statement in §3
and §6, deleting a hypothesis makes it FALSE. This is `AERWF` becoming
DERIVABLE, and the last theorem is the relational index fact `EC1-T017` asks
for, obtained through the live premise rather than through `EC1-T016`. -/

/-- **`EC1-T016`, replaced.** On a well-formed program the DECLARED row IS the
synthesized one, on the nose — not merely up to spelling. -/
theorem aer_synthesis_agrees (r : RawProgram) (h : ProgramWF r) :
    r.declaredE = synthE r :=
  (canon_of_ascending h.1).symm.trans h.2

/-- Clause 3 (`RowsWF`, canonicality) is necessary: this program satisfies
clause 11 alone and declares a PERMUTED row. -/
def declPerm : RawProgram := { ops := [⟨7⟩, ⟨9⟩], declaredE := [9, 7] }

theorem agreement_needs_RowsWF :
    ¬ ∀ r : RawProgram, AERWF r → r.declaredE = synthE r := fun h =>
  absurd (h declPerm rfl) (by decide)

/-- Clause 11 (`AERWF`) is necessary: this program has a canonical but WRONG
declared row. -/
def declShort : RawProgram := { ops := [⟨7⟩], declaredE := [] }

theorem agreement_needs_AERWF :
    ¬ ∀ r : RawProgram, RowsWF r → r.declaredE = synthE r := fun h =>
  absurd (h declShort (by simp [RowsWF, declShort])) (by decide)

/-- What `EC1-T017` actually needs, derived. Note the route: through
`aer_synthesis_agrees`, i.e. through the LIVE premise. This is the edge
`EC1-T017` should depend on, in place of the `EC1-T016` it currently names. -/
theorem checked_index_satisfies_synthesis (r : RawProgram) (h : ProgramWF r) :
    SynthE r r.declaredE :=
  (aer_synthesis_agrees r h) ▸ synthE_is_a_solution r

/-- And §6 then PINS that index: on a well-formed program the declared row is
the unique canonically spelled solution. This is the estate's own idiom —
existence plus separation, the pair `Cas/Schema/Declarations.lean:288`
(`General.row_surjective`) with `:297` (`General.row_inj`) — never `exists!`
over a Lean function. -/
theorem declared_row_is_the_unique_canonical_solution
    (r : RawProgram) (h : ProgramWF r) :
    (Ascending r.declaredE ∧ SynthE r r.declaredE) ∧
      ∀ e, Ascending e ∧ SynthE r e → e = r.declaredE := by
  have hsol : Ascending r.declaredE ∧ SynthE r r.declaredE :=
    ⟨h.1, checked_index_satisfies_synthesis r h⟩
  refine ⟨hsol, ?_⟩
  intro e he
  obtain ⟨x, _, huniq⟩ := T016_canonical_unique r
  rw [huniq e he, huniq r.declaredE hsol]

#print axioms aer_synthesis_agrees
#print axioms agreement_needs_RowsWF
#print axioms agreement_needs_AERWF
#print axioms checked_index_satisfies_synthesis
#print axioms declared_row_is_the_unique_canonical_solution

end EC1T016
