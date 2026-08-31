import Cas.Lang.Defun
import Cas.Lang.RefusalMap

/-!
# Effect Core v1 — scout probe for `EC1-T017 checked_aer_exact`

Row under scout (`PROOF-DAG.md:219`):

```text
EC1-T017  checked_aer_exact : p : CheckedProgram aer -> SynthAER (erase p) aer
          depends on: T010, T016
```

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/scout-T017.lean
```

This file is a SCOUT probe. It settles three questions and nothing else.

* §1  Under the FUNCTIONAL reading of `SynthAER` (its graph), `T017` is a
      two-field projection: `Eq.trans` of the `AERWF` clause with the index
      equation. It uses neither `check` (so not `T010`) nor uniqueness
      (so not `T016`).
* §2  Under that same reading `T016 aer_synthesis_unique` is premise-free —
      the `ProgramWF` hypothesis is dead weight, exactly the class the packet
      already deleted at `EC1-T003 pure_eval_total`.
* §3  At the estate's own CAS carrier, a per-operation synthesized error row
      STRICTLY over-approximates the row any run can realize, on an
      admissible one-line table. So no reading of `checked_aer_exact` that
      means "exact against runs" can be true; the honest content is static
      agreement.

§1 and §2 are stated over a MINIATURE stand-in (`Raw`/`Checked`), because
`RawProgram`, `ProgramWF`, `CheckedProgram`, and `SynthAER` do not exist yet
in `formal/effect-core-v1`. Their conclusion is about the SHAPE the packet
proposes, not about a declaration that has been written. §3 uses only shipped
`Cas.Lang` objects and is a claim about the CAS sublanguage.

Nothing here discharges `EC1-T017`, `EC1-T016`, or any other PENDING row.
-/

namespace ScoutT017

/-! ## §1 — the functional reading makes `T017` a field projection

A miniature with the packet's proposed shape:

* `ALGEBRA.md:295-317` — `ProgramWF` is a conjunction of named clauses, of
  which clause 11 is `AERWF`: "synthesized `A/E/R` normalizes to the declared
  triple";
* `ALGEBRA.md:320` — "`CheckedProgram A E R` stores an erased raw value,
  normalized lookup tables, and evidence of `ProgramWF`".

`Aer` stands for `EC1-D005 AER`; `synth` stands for the checker's computed
synthesizer. Every other `ProgramWF` clause is elided as `other`, because the
point is that `T017` touches only `aerWF`. -/

section Functional

/-- Stand-in for `EC1-D005 AER`. -/
abbrev Aer := Nat

/-- Stand-in for `EC1-D020 RawProgram`: a declared triple plus a body the
synthesizer reads. -/
structure Raw where
  declared : Aer
  body : List Nat
  deriving DecidableEq

/-- Stand-in for the checker's computed `A/E/R` synthesizer. Its body is
irrelevant; only its FUNCTIONALITY is used below. -/
def synth (r : Raw) : Aer := r.body.foldl (· + ·) 0

/-- `ALGEBRA.md:316` clause 11, `AERWF`. -/
def AERWF (r : Raw) : Prop := synth r = r.declared

/-- Stand-in for `EC1-D021 ProgramWF`, carrying `AERWF` and an opaque
remainder standing for clauses 1-10 and 12. -/
structure WF (r : Raw) : Prop where
  aerWF : AERWF r
  other : True

/-- Stand-in for `EC1-D023 CheckedProgram aer`. -/
structure Checked (aer : Aer) where
  raw : Raw
  wf : WF raw
  idx : raw.declared = aer

/-- Stand-in for `EC1-D025 erase`. -/
def erase {aer : Aer} (p : Checked aer) : Raw := p.raw

/-- `SynthAER` read as the GRAPH of the synthesizer — the reading the row's
`exists!` sibling `T016` presupposes if it is to be about a function. -/
def SynthAERFun (r : Raw) (a : Aer) : Prop := synth r = a

/-- **The finding.** Under the functional reading, `EC1-T017` is
`Eq.trans` of two structure fields. There is no induction, no case
analysis, and no appeal to the checker: `check` does not occur in the
statement, so `T010` is not used, and uniqueness does not occur, so `T016`
is not used. The row is DEFINITIONAL BOOKKEEPING, not a theorem. -/
theorem T017_is_a_two_field_projection {aer : Aer} (p : Checked aer) :
    SynthAERFun (erase p) aer :=
  p.wf.aerWF.trans p.idx

/-- The same fact with the dependencies made visible: the proof term
mentions exactly `aerWF` and `idx`. -/
example {aer : Aer} (p : Checked aer) : synth p.raw = aer :=
  Eq.trans p.wf.aerWF p.idx

end Functional

/-! ## §2 — the functional reading also makes `T016` premise-free

`EC1-T016 aer_synthesis_unique : ProgramWF r -> exists! aer, SynthAER r aer`.
The `ProgramWF` premise does no work when `SynthAER` is a graph. This is the
class recorded at `2026-08-31-effect-core-local-anchors.md` §3 for
`EC1-T003`, `EC1-T035`, `EC1-T115`, restated at the AER carrier. -/

section Vacuity

/-- The general shape: any Lean function's graph is uniquely inhabited at
every point, with no hypothesis at all. -/
theorem graph_of_a_function_is_unique {α β : Type} (f : α → β) (x : α) :
    ∃ y, f x = y ∧ ∀ z, f x = z → z = y :=
  ⟨f x, rfl, fun _ h => h.symm⟩

/-- `T016` at the miniature, WITHOUT the `ProgramWF` premise the row states.
Since the premise-free statement is provable, the premise cannot be
load-bearing. -/
theorem T016_needs_no_wf_premise (r : Raw) :
    ∃ a : Aer, SynthAERFun r a ∧ ∀ b, SynthAERFun r b → b = a :=
  graph_of_a_function_is_unique synth r

/-- And so the row as stated follows from the premise-free one, discarding
its hypothesis. -/
theorem T016_as_stated (r : Raw) (_h : WF r) :
    ∃ a : Aer, SynthAERFun r a ∧ ∀ b, SynthAERFun r b → b = a :=
  T016_needs_no_wf_premise r

end Vacuity

/-! ## §3 — a per-operation synthesized error row over-approximates strictly

`ALGEBRA.md:116` and `PLAN.md:228 EC1-R27`: exact `E` is synthesized from
checked `OpDesc.errorRow` values, never from `PProg.envelope`
(`EC1-CE008`). `EC1-T108` states the CAS instance of that synthesis:
`staticAER (injectCas p).E = synthesized injected OpDesc error rows`.

An `OpDesc.errorRow` is indexed by the OPERATION, not by the occurrence and
its operands (`ALGEBRA.md:131-141`). The estate already fixes the `put`
operation's admission row: `Refusal.admissionClauses = [.dangling, .wrongKind]`
(`Cas/Lang/RefusalMap.lean:163`), and `Refusal.ofAdmission_clause`
(`Cas/Lang/RefusalMap.lean:165`) proves the admission judgment lands exactly
there.

Below, `synthE` is that per-operation union at the CAS carrier and
`RealizableE` is the run-side set. The witness is a REFERENCE-FREE put: an
admissible one-line table whose synthesized row contains `.dangling` while no
run at any address function and any word can refuse with that clause. -/

section CasRow

open Cas Cas.Lang

/-- The per-operation MAY row, one entry per `PLine` constructor. The `put`
arm is the estate's own admission row plus the two non-admission ways
`referenceHandler`'s put clause refuses (`Cas/Lang/Handler.lean:78-88`); the
`load` arm is that clause's only refusal. -/
def lineClauses : PLine → List Refusal.Clause
  | .put _ _ _ _ => Refusal.admissionClauses ++ [.collision, .notWellFormed]
  | .load _ => [.noObject]

/-- The synthesized error row of a table: the union over its operations.
This is the shape `EC1-T108` prescribes — from operations, not the
envelope. -/
def synthE (p : PProg) : List Refusal.Clause := p.flatMap lineClauses

/-- The run-side row: a clause is realizable when SOME address function and
SOME starting word make the table refuse with it. -/
def RealizableE (p : PProg) (c : Refusal.Clause) : Prop :=
  ∃ (H : Bytes → Addr32) (w : Word) (r : Refusal),
    (runP H p w).1 = .refused r ∧ r.clause = c

/-- The witness: one reference-free put. Admissible — nonempty, no answer
indices, so no dangling-index and no empty-table refusal. -/
def freeput : PProg := [.put 0 0 [] []]

/-- The synthesized row declares `.dangling`, because the `put` OPERATION's
admission row does. -/
theorem dangling_is_synthesized : Refusal.Clause.dangling ∈ synthE freeput := by
  decide

/-- The node this table admits carries no references, so `checkRefs` on it
is `.ok` and `Cas.put` cannot return an admission error
(`put_error_iff`, `Cas/Core/Admission.lean:187`). -/
theorem freeput_node_never_fails_admission
    (H : Bytes → Addr32) (w : Word) (h : Node.WF ⟨0, 0, [], []⟩) :
    ∀ e, Cas.put H (Word.toStore w) ⟨⟨0, 0, [], []⟩, h⟩ ≠ .error e := by
  intro e he
  have := put_error_iff.mp he
  simp [Cas.checkRefs] at this

/-- Reading the run off the table: `freeput` refuses exactly when its single
put refuses, with the same refusal. -/
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

/-- The put clause of `referenceHandler` on a reference-free node cannot
produce an admission refusal. -/
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

/-- No run of `freeput`, at any address function and any word, refuses with
clause `.dangling`. -/
theorem freeput_never_refuses_dangling
    (H : Bytes → Addr32) (w : Word) (r : Refusal)
    (h : (runP H freeput w).1 = .refused r) :
    r.clause ≠ Refusal.Clause.dangling :=
  putWord_freeput_never_dangles H w r (freeput_refusal_is_the_put_refusal H w r h)

/-- **The finding.** The per-operation synthesized error row STRICTLY
over-approximates the realizable one, on an admissible table. Any statement
of `EC1-T017` whose "exact" means "exact against runs" is therefore FALSE at
the CAS sublanguage; `EC1-K11`'s caveat ("exact for the checked static
judgment, not that every error ... occurs on every runtime path",
`CONTRACT-PACKET.md:340`) is load-bearing, not a hedge. -/
theorem freeput_dangling_is_declared_but_unrealizable :
    Refusal.Clause.dangling ∈ synthE freeput
      ∧ ¬ RealizableE freeput .dangling := by
  refine ⟨dangling_is_synthesized, ?_⟩
  rintro ⟨H, w, r, hrun, hcl⟩
  exact freeput_never_refuses_dangling H w r hrun hcl

theorem synthE_strictly_over_approximates :
    ∃ (p : PProg) (c : Refusal.Clause),
      c ∈ synthE p ∧ ¬ RealizableE p c :=
  ⟨freeput, .dangling, freeput_dangling_is_declared_but_unrealizable⟩

/-! The direction is over-approximation, not unsoundness: the synthesized row
is strictly LARGER than the run-side row, which is the safe direction for a
declared type. `EC1-F09` attacks the other direction (a too-small `E`). -/

end CasRow

/-! ## §4 — the AER fixpoint terminates only up to row canonicalization

`ALGEBRA.md:284` — "Cycles are ordinary references to earlier blocks."
So the `E`/`R` halves of `SynthAER` are a fixpoint over a CYCLIC finite
graph, not a structural recursion, and clause 11 `AERWF` is decidable only if
that fixpoint is reached in finitely many steps.

The one-block self-loop below shows the iteration does NOT stabilize when
rows are carried as raw lists, and DOES stabilize immediately when each step
canonicalizes. So clause 3 `RowsWF` ("all rows are canonical") is not
cosmetic: in the frozen fail-fast clause order it is a PRECONDITION for
clause 11 being decidable at all. This is the same premise `R16` part 2 and
`EC1-CE030` force on row normalization, arriving here from a second
direction. -/

section RowFixpoint

/-- Propagation on a single self-looping block whose own row is `[0]`,
with rows carried as raw lists. -/
def loopIter : Nat → List Nat
  | 0 => [0]
  | k + 1 => [0] ++ loopIter k

theorem loopIter_length (k : Nat) : (loopIter k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [loopIter, ih]

/-- **The finding.** With raw rows the fixpoint iteration never reaches a
fixed point, so no bounded-iteration decision procedure exists for clause 11
on that carrier. -/
theorem loopIter_never_stabilizes (k : Nat) : loopIter k ≠ loopIter (k + 1) := by
  intro h
  have hl := congrArg List.length h
  rw [loopIter_length, loopIter_length] at hl
  omega

/-- Duplicate-free insertion; the minimal row canonicalizer. -/
def ins (t : Nat) (xs : List Nat) : List Nat := if t ∈ xs then xs else t :: xs

/-- The same propagation with each step canonicalized. -/
def loopIterCanon : Nat → List Nat
  | 0 => [0]
  | k + 1 => ins 0 (loopIterCanon k)

/-- Canonicalized, the same iteration is stationary from step zero, so the
bounded-iteration decision procedure exists. -/
theorem loopIterCanon_stable (k : Nat) : loopIterCanon k = [0] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [loopIterCanon, ih, ins]

theorem loopIterCanon_reaches_a_fixpoint (k : Nat) :
    loopIterCanon k = loopIterCanon (k + 1) := by
  rw [loopIterCanon_stable, loopIterCanon_stable]

/-! NOT PROVED HERE: a termination BOUND for the general multi-block case.
Stabilization at some `k` follows from finiteness of the per-program tag and
service universes plus monotonicity, and that argument is exactly what the
existence half of `EC1-T016` owes. This section proves only that
canonicalization is necessary, not that it is sufficient. -/

end RowFixpoint

end ScoutT017

/-! ## Kernel receipts -/

#print axioms ScoutT017.T017_is_a_two_field_projection
#print axioms ScoutT017.graph_of_a_function_is_unique
#print axioms ScoutT017.T016_needs_no_wf_premise
#print axioms ScoutT017.T016_as_stated
#print axioms ScoutT017.dangling_is_synthesized
#print axioms ScoutT017.freeput_node_never_fails_admission
#print axioms ScoutT017.freeput_refusal_is_the_put_refusal
#print axioms ScoutT017.putWord_freeput_never_dangles
#print axioms ScoutT017.freeput_never_refuses_dangling
#print axioms ScoutT017.freeput_dangling_is_declared_but_unrealizable
#print axioms ScoutT017.synthE_strictly_over_approximates
#print axioms ScoutT017.loopIter_never_stabilizes
#print axioms ScoutT017.loopIterCanon_stable
#print axioms ScoutT017.loopIterCanon_reaches_a_fixpoint
