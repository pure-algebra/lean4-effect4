import Cas.Core.Admission
import Cas.Backend.Canon

/-!
# Effect Core v1 — `EC1-T012`, the admission boundary's error branch

Slice `EC1-S2`. Written 2026-08-31 against the working tree, Lean
`leanprover/lean4:v4.33.1`. Nothing here is proposed for `library/` or for
`formal/effect-core-v1/EffectCore/Admission/Check.lean`, which is still the
reserved empty scaffold (verified: doc comment plus
`namespace EffectCore.Admission` / `end`, no declarations).

Run it:

```
cd library/cas
lake env lean ../../.staging/effect-core-v1/workshop/s2/T012.lean
```

The row under implementation, verbatim from `PROOF-DAG.md:214`:

```
EC1-T012  check_error_iff : (exists d, check r = error d) <-> not ProgramWF r
          depends on: T010,T011; decidable WF
```

Lean skill stage followed: `lean-algebraic-systems` (the checker is an
operation over a program carrier, not a representation layer). Its gate asks for
a contract naming operations, observables, invalid scenarios and environment
assumptions; none exists — `EC1-D020`–`EC1-D024` are `PROPOSED TERM` prose rows
— so the stage's own instruction was followed: a provisional contract is
returned inline, as the §6 carrier, with its alternatives named. Proof route
taken from that stage's `references/proof-tool-routing.md`: *pure recursive
interpreter/fold — structural induction and simp lemmas for constructors*,
which is also `PROOF-DAG.md:518`'s Checker row ("structural recursion plus
decidable per-clause reflection"). The prohibited shortcut for that family —
"using successful examples as completeness" — is not taken: §6's completeness is
`checkClauses_ok_iff`'s `mpr`, quantified over every `RawProgram`. The examples
in §5 and §6 are used only to REFUTE, which is their sound direction.

| § | Claim | Receipt |
|---|---|---|
| 1 | `EC1-T012` holds for any `check` satisfying `EC1-T010` and `EC1-T011`, over arbitrary carriers, with NO decidability hypothesis. | `check_error_iff`, axiom-free |
| 2 | `decidable WF` is a CONSEQUENCE of T010+T011, computably. The DAG's dependency arrow at `:214` points the wrong way. | `decidableOfAdequate`, `accepts_iff`, axiom-free |
| 2 | The `:221` prohibition cannot fire as an elaboration failure. The only kernel-visible gate is the axiom receipt. | `decidability_is_never_an_obstruction`, `[Classical.choice]` — reporting it IS the result |
| 3 | Neither half of the iff is deletable. | `forward_needs_completeness`, `backward_needs_soundness`, axiom-free |
| 4 | `EC1-T012` IS `EC1-T011` plus a double-negated `EC1-T010`, exactly. So T012 gives T011 outright, and gives T010 only with decidability. | `errorIff_iff_complete_and_weakSound`, `complete_of_errorIff`, `sound_of_weakSound_of_decidable` — all axiom-free |
| 5 | A checker that NORMALIZES BEFORE IT DECIDES makes `EC1-T012` FALSE, not merely unproved — exhibited at the estate's shipped normalizer. | `T012_fails_for_normalize_then_check` |
| 6 | At a concrete three-clause `RawProgram`/`ProgramWF`/`Diagnostic`/`CheckedProgram`/`check`, all three rows hold and T010 is not a projection. | `check_sound`, `check_complete`, `check_error_iff'` |
| 7 | T012 holds at the estate's shipped fail-fast checker, and hands back `Decidable (RefsOk σ rs)`. | `checkRefs_error_iff`, `decidableRefsOk` |
| 8 | T012 fixes accept/reject and NOTHING about which diagnostic. | `T012_does_not_determine_the_diagnostic`, `checkClauses_reports_only_the_first` |

Standing law honoured. `R16` part 1: the diagnostic is quantified
EXISTENTIALLY throughout, which is the first-error-compatible shape; §6's
checker is `firstError` over a frozen clause order and §8 carries the
`EC1-CE031` receipt at that carrier. `R16` part 2 / `EC1-CE030`: §5 is that row
arriving at T012's own backward half. `R15`/`EC1-CE033`: `check` is
`Except`-valued throughout; a total checker would have no error arm and §1 would
not typecheck. `R4`: no clause below is stated denotationally.

Axioms. Every declaration carries a `#print axioms` receipt in §9. The ceiling
is `[propext, Quot.sound]`; fifteen receipts are axiom-free, including the row's
own abstract proof. `Classical.choice` appears in exactly FOUR receipts, all
declared: `decidability_is_never_an_obstruction`, where reporting it IS the
finding; and the three §5 theorems downstream of `Cas/Backend/Canon.lean:167`
`nodup_keys_canonServices`, whose `List.mergeSort` chain is the ceiling
`EC1-CE030` already records for this normalizer. Nothing authored here
introduces it, and §5's own abstract obligation
(`normalize_then_check_forbids_creation`) is axiom-free. No `sorry`, no `axiom`,
no `native_decide`, no `#eval` standing for a claim.
-/

set_option warn.classDefReducibility false

namespace EffectCoreS2T012

/-! ## §1 — The row, at the shape `EC1-D024` declares and nothing more

`EC1-D024` fixes `check : RawProgram -> Except Diagnostic (Sigma CheckedProgram)`.
`EC1-T012` reads only the two arms of that `Except`. So the row is provable
before any carrier exists, and the proof below quantifies over arbitrary `R`,
`D`, `C` and an arbitrary predicate `WF`. There is no `Decidable` anywhere in
scope.

`Sound` is `EC1-T010`; `Complete` is `EC1-T011` with the `Sigma` bound
EXISTENTIALLY (see `divergenceFromDag`: the DAG row leaves the alphabet `a`
free, which is a scope defect, not a strengthening). -/

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

/-! ## §2 — `decidable WF` is the consequence, not the premise

`PROOF-DAG.md:214` lists `decidable WF` in T012's dependency column and
`:213` lists "decidability of every WF clause" in T011's. The second is right;
the first double-counts it. The checker IS the decision procedure, and the
construction below is a computable `def` reporting no axioms at all. -/

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

/-- The characteristic function of `WF`, read off the checker. -/
theorem accepts_iff {WF : R → Prop} {chk : R → Except D C}
    (hs : Sound WF chk) (hc : Complete WF chk) (r : R) :
    accepts chk r = true ↔ WF r := by
  unfold accepts
  cases hx : chk r with
  | ok c => exact ⟨fun _ => hs r c hx, fun _ => rfl⟩
  | error d =>
    constructor
    · intro h; exact nomatch h
    · intro hwf; exact absurd hwf ((check_error_iff hs hc r).mp ⟨d, hx⟩)

/-- **The prohibition at `PROOF-DAG.md:221` cannot fire as a typechecking
failure.** Classically every proposition is `Decidable`, so `DecidablePred P` is
inhabited for an arbitrary `P` — however semantic the twelve `ProgramWF` clauses
become, nothing in the elaborator will notice.

The receipt below reports `Classical.choice`, and REPORTING IT IS THE RESULT.
The only kernel-visible gate on `:221` is therefore the axiom receipt itself:
`check` must be a computable `def`, never `noncomputable`, and
`#print axioms check_complete` must not show `Classical.choice`. That gate
belongs in the dispatch brief, because nothing else will catch a violation. -/
theorem decidability_is_never_an_obstruction (P : R → Prop) :
    Nonempty (DecidablePred P) :=
  ⟨fun r => Classical.propDecidable (P r)⟩

end Decidability

/-! ## §3 — Neither half of the iff is deletable

Two one-point counterexamples, so that a later lane cannot "simplify"
`EC1-T012` into one implication and keep the name. -/

section Independence

private def rejector : Unit → Except Unit Unit := fun _ => .error ()
private def acceptor : Unit → Except Unit Unit := fun _ => .ok ()

/-- The forward half genuinely consumes `EC1-T011`. An always-rejecting checker
is vacuously SOUND for `fun _ => True`, and errors on a well-formed input. -/
theorem forward_needs_completeness :
    Sound (fun _ : Unit => True) rejector ∧
      ¬ (∀ r : Unit, (∃ d, rejector r = .error d) → ¬ (fun _ : Unit => True) r) := by
  refine ⟨fun _ _ _ => trivial, ?_⟩
  intro hall
  exact hall () ⟨(), rfl⟩ trivial

/-- The backward half genuinely consumes `EC1-T010`. An always-accepting checker
is vacuously COMPLETE for `fun _ => False`, and rejects nothing. -/
theorem backward_needs_soundness :
    Complete (fun _ : Unit => False) acceptor ∧
      ¬ (∀ r : Unit, ¬ (fun _ : Unit => False) r → ∃ d, acceptor r = .error d) := by
  refine ⟨fun _ h => h.elim, ?_⟩
  intro hall
  obtain ⟨d, hd⟩ := hall () (fun h => h)
  exact nomatch hd

end Independence

/-! ## §4 — Three rows, two facts — and the trade is ASYMMETRIC

`EC1-T010`, `EC1-T011` and `EC1-T012` are not three independent obligations, and
the accounting is sharper than "three rows, two facts".

`EC1-T012` implies `EC1-T011` ON ITS OWN, constructively. It implies `EC1-T010`
too, but only given `Decidable (WF r)`: `ErrorIff` delivers `¬ ¬ WF r` in the
`ok` arm, and nothing constructive turns that into `WF r`. So `EC1-T012` is the
STRONGEST of the three, and the decidability the DAG attaches to it as a
dependency is really the price of the recovery in the other direction — the
recovery of `EC1-T010` FROM `EC1-T012`, which is not what `:214` says it is
for. -/

section Trade

variable {R D C : Type}

/-- **`EC1-T012` gives `EC1-T011` OUTRIGHT**, constructively, consuming nothing
else — not `EC1-T010` and not decidability. The `Sound` hypothesis the row's
dependency column would suggest is not merely unnecessary here, it is
unmentionable: the proof never has anywhere to put it. -/
theorem complete_of_errorIff {WF : R → Prop} {chk : R → Except D C}
    (h : ErrorIff WF chk) : Complete WF chk := by
  intro r hw
  cases hx : chk r with
  | ok c => exact ⟨c, rfl⟩
  | error d => exact absurd hw ((h r).mp ⟨d, hx⟩)

/-- `EC1-T011` + `EC1-T012` give `EC1-T010` — but only with a decision for `WF`.
The `isFalse` arm is where the recovery happens; the `isTrue` arm never consults
the checker at all. -/
theorem sound_of_errorIff_of_decidable {WF : R → Prop} {chk : R → Except D C}
    (inst : DecidablePred WF) (h : ErrorIff WF chk) : Sound WF chk := by
  intro r c hx
  cases inst r with
  | isTrue hw => exact hw
  | isFalse hn =>
    obtain ⟨d, hd⟩ := (h r).mpr hn
    rw [hx] at hd
    exact nomatch hd

/-- `EC1-T010` weakened to its double negation. This is the EXACT amount of
`EC1-T010` that `EC1-T012` carries, and naming it is what makes the accounting
below an equivalence rather than a pair of one-way implications. -/
def WeakSound (WF : R → Prop) (chk : R → Except D C) : Prop :=
  ∀ (r : R) (c : C), chk r = .ok c → ¬ ¬ WF r

theorem weakSound_of_sound {WF : R → Prop} {chk : R → Except D C}
    (hs : Sound WF chk) : WeakSound WF chk := fun r c h hn => hn (hs r c h)

theorem sound_of_weakSound_of_decidable {WF : R → Prop} {chk : R → Except D C}
    (inst : DecidablePred WF) (hw : WeakSound WF chk) : Sound WF chk := fun r c h =>
  match inst r with
  | isTrue hy  => hy
  | isFalse hn => ((hw r c h) hn).elim

/-- **The exact content of `EC1-T012`.** The row is `EC1-T011` in full, plus
`EC1-T010` double-negated, and nothing else. Constructive in both directions.

Three consequences for `PROOF-DAG.md:212-214`.

* `EC1-T011` is not a dependency of `EC1-T012`, it is a CONJUNCT of it. Landing
  T012 lands T011; the DAG bills them separately.
* `EC1-T010` is a dependency in the honest sense — but only through its weak
  form, which is why recovering the full `EC1-T010` from `EC1-T012` is exactly
  where `Decidable (WF r)` is spent (`sound_of_weakSound_of_decidable`).
* `decidable WF` therefore belongs on no edge INTO `EC1-T012`. It is the price
  of one edge OUT of it. -/
theorem errorIff_iff_complete_and_weakSound {WF : R → Prop} {chk : R → Except D C} :
    ErrorIff WF chk ↔ (Complete WF chk ∧ WeakSound WF chk) := by
  constructor
  · intro h
    refine ⟨complete_of_errorIff h, ?_⟩
    intro r c hx hn
    obtain ⟨d, hd⟩ := (h r).mpr hn
    rw [hx] at hd
    exact nomatch hd
  · rintro ⟨hc, hw⟩ r
    refine ⟨not_wf_of_error hc, ?_⟩
    intro hn
    cases hx : chk r with
    | ok c => exact absurd hn (hw r c hx)
    | error d => exact ⟨d, rfl⟩

end Trade

/-! ## §5 — The ORDER OBLIGATION lands on `EC1-T012`'s own backward half

`EC1-K10` (`CONTRACT-PACKET.md:306-310`) requires
`erase checked = normalizeRaw (erase checked)`, while `EC1-T012`'s statement is
about the RAW input `r`. Read together they invite a checker that normalizes and
then decides. `EC1-CE030`/`R16` part 2 is filed against row normalization; what
follows is that row arriving here, one step harder than it lands on `EC1-T010`.

At `EC1-T010` the consequence is that the row cannot be PROVED. At `EC1-T012`
the consequence is that the row is FALSE: normalization does not merely fail to
transport well-formedness backwards, it CREATES well-formedness, so an
ill-formed raw program is ACCEPTED and the backward half `¬ ProgramWF r →
∃ d, check r = .error d` has a counterexample.

Proved at `Cas/Backend/Canon.lean`'s shipped keyed-row normalizer, not at a toy. -/

section OrderObligation

open Cas.Backend Cas.Schema

variable {R D C : Type}

/-- **The obligation, abstractly.** If `chk₀` is adequate for `WF` and the
deployed checker is `chk₀ ∘ norm`, then `EC1-T012` against the RAW predicate
forces normalization never to CREATE the predicate. Constructive: the
counterexample below contradicts the conclusion directly, so no
double-negation elimination is needed anywhere. -/
theorem normalize_then_check_forbids_creation
    {WF : R → Prop} {chk₀ : R → Except D C} {norm : R → R}
    (hs : Sound WF chk₀) (hc : Complete WF chk₀)
    (h : ∀ r : R, (∃ d, chk₀ (norm r) = .error d) ↔ ¬ WF r)
    {r : R} (hraw : ¬ WF r) : ¬ WF (norm r) :=
  (check_error_iff hs hc (norm r)).mp ((h r).mpr hraw)

/-- `ProgramWF` clause 1 (`IdsWF`, `ALGEBRA.md:296`, "every table is
duplicate-free") at the estate's shipped keyed-row carrier. -/
def NodupKeys (xs : List ServiceRef) : Prop := (xs.map (·.key)).Nodup

instance instDecNodupKeys (xs : List ServiceRef) : Decidable (NodupKeys xs) :=
  inferInstanceAs (Decidable ((xs.map (·.key)).Nodup))

/-- A single first-error diagnostic for the clause (`R16` part 1: one value, not
a set, not a `NonEmpty`). -/
inductive DupDiag where
  | duplicateKeys
  deriving DecidableEq, Repr

/-- The clause DECIDED ON THE RAW INPUT — the order `EC1-T010` and `EC1-T012`
both require. -/
def rawChecker (xs : List ServiceRef) : Except DupDiag Unit :=
  if NodupKeys xs then .ok () else .error .duplicateKeys

theorem rawChecker_sound : Sound NodupKeys rawChecker := by
  intro xs u h
  by_cases hn : NodupKeys xs
  · exact hn
  · rw [rawChecker, if_neg hn] at h; exact nomatch h

theorem rawChecker_complete : Complete NodupKeys rawChecker := by
  intro xs h
  exact ⟨(), by rw [rawChecker, if_pos h]⟩

/-- The positive boundary: decide on the raw input and `EC1-T012` holds exactly.
This is the checker order the row forces. -/
theorem rawChecker_error_iff : ErrorIff NodupKeys rawChecker :=
  check_error_iff rawChecker_sound rawChecker_complete

/-- The SAME clause, decided on the normal form — the order `EC1-K10` invites. -/
def normThenCheck (xs : List ServiceRef) : Except DupDiag Unit :=
  rawChecker (canonServices xs)

private def dupL : ServiceRef := { key := "k", name := "L", path := "l" }
private def dupR : ServiceRef := { key := "k", name := "R", path := "r" }

/-- Two rows, one key: the raw table that fails clause 1. -/
private def dupTable : List ServiceRef := [dupL, dupR]

theorem dupTable_not_nodup : ¬ NodupKeys dupTable := by
  simp [NodupKeys, dupTable, dupL, dupR]

/-- `Cas/Backend/Canon.lean:167` `nodup_keys_canonServices`: normalization does
not PRESERVE the duplicate-free clause, it ESTABLISHES it, whatever the input
was. Inherits `Classical.choice` from the `List.mergeSort` chain — the ceiling
`EC1-CE030` already records for this normalizer. -/
theorem norm_always_nodup (xs : List ServiceRef) : NodupKeys (canonServices xs) :=
  nodup_keys_canonServices xs

theorem normThenCheck_accepts_dupTable : normThenCheck dupTable = .ok () := by
  rw [normThenCheck, rawChecker, if_pos (norm_always_nodup dupTable)]

/-- **`EC1-T012` IS FALSE for a checker that normalizes before it decides.**

`dupTable` violates clause 1, and `normThenCheck` accepts it, so the backward
half of the row has a counterexample at live estate code. The row is not
"unproved pending a transfer lemma" — it is refuted for that checker.

Forced repair, and it is a constraint on the IMPLEMENTATION rather than on the
statement: every clause is decided on the raw input, and `normalizeRaw` sits
strictly INSIDE the `CheckedProgram` payload, after the decision. §6's `check`
is built that way. -/
theorem T012_fails_for_normalize_then_check :
    ¬ ((∃ d, normThenCheck dupTable = .error d) ↔ ¬ NodupKeys dupTable) := by
  intro h
  obtain ⟨d, hd⟩ := h.mpr dupTable_not_nodup
  rw [normThenCheck_accepts_dupTable] at hd
  exact nomatch hd

end OrderObligation

/-! ## §6 — A concrete carrier, and the row proved at it

Everything above is carrier-independent, which is exactly why `EC1-T012` is the
one Admission row invariant under the packet's unresolved spellings of
`EC1-D022` (`Diagnostic` vs `CheckDiagnostic` vs the workshop's
`NonEmpty Diagnostic`): the row only asks `∃ d`.

But a carrier-independent theorem cannot show the row is non-vacuous at a real
checker, so this section supplies the MINIMUM `RawProgram`, `ProgramWF`,
`Diagnostic`, `CheckedProgram` and `check` the row needs, and proves T010, T011
and T012 at them. It is three clauses, not twelve; see `divergenceFromDag`.

Two vacuity traps are deliberately avoided.

* `check` is NOT `dite (decide (ProgramWF r))`. It is `firstError` over three
  clause decisions defined INDEPENDENTLY of `ProgramWF`, and `check_sound` is
  their composition through `checkClauses_ok_iff`. Were it the `dite`,
  `check_sound` would be `Subtype.property` and prove nothing.
* `ProgramWF`'s three clauses are stated SYNTACTICALLY, in the predicate itself
  and not merely in the checker. Approximating a semantic clause inside `check`
  alone keeps T010 and kills T011, so the syntactic reading has to live in
  `ProgramWF`. The clause chosen here in place of `HandlersWF`'s "every REACHABLE
  operation" is a whole-table fold, which sidesteps the reachability question
  rather than answering it — recorded as an omission, not a result. -/

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

/-! ## §7 — The row at the estate's shipped fail-fast checker

`Cas/Core/Admission.lean` is the estate's one admission clause: `RefsOk` (`:35`)
is its `ProgramWF`, `checkRefs` (`:49`) is its `check`, `AdmissionError` (`:29`)
is its `Diagnostic`, and `checkRefs_ok_iff` (`:60`) carries `EC1-T010` and
`EC1-T011` in a single iff. `EC1-T012` at that scale is the instantiation below.

`decidableRefsOk` is the point of the section: `RefsOk` is a
`∀ ∈ list, ∃ ...` statement whose decidability is not visible in its syntax, and
it is the SHIPPED CHECKER that supplies it. That is `EC1-T012a` doing real work
at live code. -/

section EstateAnchor

open Cas

theorem refs_Sound (σ : Store) : Sound (RefsOk σ) (checkRefs σ) := by
  intro rs u h
  cases u
  exact checkRefs_ok_iff.mp h

theorem refs_Complete (σ : Store) : Complete (RefsOk σ) (checkRefs σ) := by
  intro rs h
  exact ⟨(), checkRefs_ok_iff.mpr h⟩

/-- `EC1-T012` at `Cas.checkRefs`. -/
theorem checkRefs_error_iff (σ : Store) (rs : List Ref) :
    (∃ e, checkRefs σ rs = .error e) ↔ ¬ RefsOk σ rs :=
  check_error_iff (refs_Sound σ) (refs_Complete σ) rs

/-- `EC1-T012a` at `Cas.checkRefs`. -/
def decidableRefsOk (σ : Store) : DecidablePred (RefsOk σ) :=
  decidableOfAdequate (refs_Sound σ) (refs_Complete σ)

/-- `R16` compatibility receipt. The shipped `checkRefs_complete` (`:137`) is
EXISTENTIAL rejection completeness — "with the first failing clause found, not
necessarily the condemning one", in its own docstring. `EC1-T012`'s forward half
is compatible with it and strictly stronger only because `checkRefs_ok_iff` is a
full iff; the row demands no per-clause diagnostic and does not resurrect the
shape `EC1-CE031` killed. -/
theorem checkRefs_error_iff_refines_shipped_completeness
    (σ : Store) (rs : List Ref) (h : ∃ e, AdmissionError.Condemns σ e rs) :
    ∃ e', checkRefs σ rs = .error e' :=
  checkRefs_complete h

end EstateAnchor

/-! ## §8 — What `EC1-T012` does NOT say

The row fixes the checker's ACCEPT/REJECT partition and nothing else. Two
receipts, so that the next lane does not read more out of it. -/

section Scope

/-- `EC1-T012` does not determine the diagnostic. Two checkers agreeing on every
accept/reject decision, disagreeing on what they report, both satisfy the row.
Consistent with `R16`/`EC1-CE031`: the reported clause is fixed by the frozen
scan order, which is `EC1-T015`'s business, not this row's. -/
theorem T012_does_not_determine_the_diagnostic :
    ∃ chk₁ chk₂ : Bool → Except Nat Unit,
      ErrorIff (fun b => b = true) chk₁ ∧ ErrorIff (fun b => b = true) chk₂ ∧
        chk₁ ≠ chk₂ := by
  refine ⟨fun b => if b then .ok () else .error 0,
          fun b => if b then .ok () else .error 1, ?_, ?_, ?_⟩
  · intro b; cases b <;> simp
  · intro b; cases b <;> simp
  · intro h
    have := congrFun h false
    simp at this

/-- `R16` part 1 at §6's carrier: when the first clause condemns, that is the
only diagnostic reported, whatever the later clauses say. `EC1-CE031` in the
Effect Core shape. -/
theorem checkClauses_reports_only_the_first
    (r : RawProgram) (d : Diagnostic) (h : idsClause r = some d) :
    checkClauses r = .error d := by
  rw [checkClauses, h]
  rfl

/-- A raw program condemned by TWO clauses — duplicate block ids and a missing
entry — for which the checker returns only the first. The `EC1-CE031` witness
transported to §6's carrier. -/
def doublyBad : RawProgram :=
  { blocks := [⟨0, [], []⟩, ⟨0, [], []⟩], entry := 7, resultTy := 0,
    declaredAER := ⟨0, []⟩ }

theorem doublyBad_violates_ids : ¬ IdsWF doublyBad := by
  rintro ⟨hnd, -⟩
  simp [doublyBad] at hnd

theorem doublyBad_violates_entry : ¬ EntryWF doublyBad := by
  simp [EntryWF, doublyBad]

theorem doublyBad_reports_only_the_id_clause :
    checkClauses doublyBad = .error (.duplicateBlockId 0) := rfl

/-- And the row still holds of it, because the row only asks `∃ d`. -/
theorem doublyBad_error_iff : (∃ d, check doublyBad = .error d) ↔ ¬ ProgramWF doublyBad :=
  check_error_iff' doublyBad

end Scope

/-! ## §9 — Axiom receipts -/

section Receipts

#print axioms not_wf_of_error
#print axioms error_of_not_wf
#print axioms check_error_iff
#print axioms decidableOfAdequate
#print axioms accepts_iff
#print axioms decidability_is_never_an_obstruction
#print axioms forward_needs_completeness
#print axioms backward_needs_soundness
#print axioms complete_of_errorIff
#print axioms sound_of_errorIff_of_decidable
#print axioms weakSound_of_sound
#print axioms sound_of_weakSound_of_decidable
#print axioms errorIff_iff_complete_and_weakSound
#print axioms normalize_then_check_forbids_creation
#print axioms rawChecker_sound
#print axioms rawChecker_complete
#print axioms rawChecker_error_iff
#print axioms dupTable_not_nodup
#print axioms norm_always_nodup
#print axioms normThenCheck_accepts_dupTable
#print axioms T012_fails_for_normalize_then_check
#print axioms dupId_none_iff
#print axioms firstDangling_none_iff
#print axioms danglingEdge_none_iff
#print axioms idsClause_none_iff
#print axioms entryClause_none_iff
#print axioms aerClause_none_iff
#print axioms firstError_ok_iff
#print axioms firstError_ok_iff3
#print axioms checkClauses_ok_iff
#print axioms check_error_iff_clauses
#print axioms check_sound
#print axioms check_complete
#print axioms check_Sound
#print axioms check_Complete
#print axioms check_error_iff'
#print axioms decidableProgramWF
#print axioms refs_Sound
#print axioms refs_Complete
#print axioms checkRefs_error_iff
#print axioms decidableRefsOk
#print axioms checkRefs_error_iff_refines_shipped_completeness
#print axioms T012_does_not_determine_the_diagnostic
#print axioms checkClauses_reports_only_the_first
#print axioms doublyBad_violates_ids
#print axioms doublyBad_violates_entry
#print axioms doublyBad_reports_only_the_id_clause
#print axioms doublyBad_error_iff

end Receipts

end EffectCoreS2T012
