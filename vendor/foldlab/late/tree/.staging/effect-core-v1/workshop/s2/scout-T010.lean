import Cas.Core.Admission
import Cas.Backend.Canon

/-!
# Effect Core v1 — scout probe for `EC1-T010` (`check_sound`)

Slice `EC1-S2`, the admission boundary. Written 2026-08-31 against the working
tree, Lean `leanprover/lean4:v4.33.1`. Scouting only: nothing here is proposed
for `library/` or for `formal/effect-core-v1/EffectCore/Admission/Check.lean`
(which is still the reserved empty scaffold).

Run it:

```
cd library/cas
lake env lean ../../.staging/effect-core-v1/workshop/s2/scout-T010.lean
```

The row under scout:

```
EC1-T010  check_sound : check r = ok <a,p> -> ProgramWF r
```

Six questions. §6 adds the composition shape the twelve-clause checker will need.

| § | Question | Answer this file establishes |
|---|---|---|
| 1 | Does the reported anchor hold? | Yes — `checkRefs_ok_iff` (`Cas/Core/Admission.lean:60`) is `T010` and `T011` in ONE iff, at one clause. |
| 2 | Is the DAG's decidability warning a caution or a theorem? | A **theorem**. `T010 ∧ T011` CONSTRUCT a decision procedure for `ProgramWF`, constructively. An undecidable clause makes `T011` FALSE, not merely hard. |
| 2b | What happens if a clause is only semi-decided? | Soundness survives the syntactic over-approximation; completeness dies at the first separating program. |
| 3 | Is `T012` a separate obligation? | No. It follows from `T010 ∧ T011` with **no** decidability premise, contrary to the DAG's stated dependency. |
| 4 | May the checker normalize before it checks? | No. Normalization CREATES the duplicate-free clause, so `ProgramWF (normalizeRaw r) → ProgramWF r` is FALSE. |
| 5 | Is `T016` vacuous? | Yes, if `SynthAER` is a function graph — the `ProgramWF` premise is provably dead weight. |

Nothing here proves anything about a `ProgramWF` that does not yet exist. §2–§6
are statements about the SHAPE any such definition must satisfy, proved at the
abstract carrier or at the estate's shipped one, and they are stated so that the
abstraction is visible rather than hidden in a name.

Axiom ceiling: the receipts at the foot of the file. No `sorry`, no `axiom`, no
`native_decide`, no `#eval` carrying a claim.

**`Classical.choice` is used, and here is where.** Exactly three receipts report
it — `norm_always_nodup`, `normalize_then_check_cannot_prove_T010`, and
`normalization_is_harmless_where_the_clause_holds`. All three inherit it from
`Cas/Backend/Canon.lean`'s `nodup_keys_canonServices` and
`canonServices_perm_of_nodup_keys`, which rest on the `List.mergeSort` family.
It is the same ceiling `EC1-CE030` already records for this exact normalizer,
and it is confined to §4. Nothing in §1, §2, §2b, §3, §5, or §6 uses it: the
decision-procedure construction in §2 reports `[propext]` only, which is the
point — a decision procedure leaning on choice would not be one.

Lean note: `ExistsUnique` / `∃!` is NOT in scope in this environment (no Mathlib
under `library/cas`), so §5 spells the unique-existence statement out. That is an
improvement for this particular row, since the vacuity is exactly what the
notation hides.
-/

namespace EffectCoreScoutT010

/-! ## §1 — the reported anchor, re-elaborated

`.staging/agent-reports/2026-08-31-effect-core-local-anchors.md` §4.2 classifies
`T010` as SPECIALIZES with anchor `Cas/Core/Admission.lean:60 checkRefs_ok_iff`.
Verified: the declaration is at that line and says what the report says.

The load-bearing observation the anchor table records but does not draw out: at
the estate's ONE admission clause, `T010` and `T011` are not two theorems. They
are the two directions of a single iff, and the iff is available because
`RefsOk` is decidable by construction. -/

section Anchor

open Cas

/-- `EC1-T010`'s shape at the estate's shipped clause: `Cas/Core/Admission.lean:60`,
forward direction. -/
theorem anchor_T010 {σ : Store} {rs : List Ref}
    (h : checkRefs σ rs = .ok ()) : RefsOk σ rs :=
  checkRefs_ok_iff.mp h

/-- `EC1-T011`'s shape at the same clause: the SAME theorem, backwards. -/
theorem anchor_T011 {σ : Store} {rs : List Ref}
    (h : RefsOk σ rs) : checkRefs σ rs = .ok () :=
  checkRefs_ok_iff.mpr h

/-- And the first-error half the packet's `R16` ruling pins:
`Cas/Core/Admission.lean:108`. A returned error's clause holds of the input —
one clause, never a set. -/
theorem anchor_first_error {σ : Store} {rs : List Ref} {e : AdmissionError}
    (h : checkRefs σ rs = .error e) : e.Condemns σ rs :=
  checkRefs_error_condemns h

end Anchor

/-! ## §2 — `T010 ∧ T011` CONSTRUCT a decision procedure

`PROOF-DAG.md:221` warns that `EC1-T011/T012` are "prohibited if any `ProgramWF`
clause is silently changed to an undecidable semantic property". That reads as
lane discipline. It is stronger than that, and the strength is provable.

`check` is a TOTAL Lean function into a two-arm sum. Given `T010` and `T011`,
its two arms decide `ProgramWF` on the nose: the `ok` arm supplies the proof,
and the `error` arm refutes it because completeness would have forced an `ok`.
No classical reasoning is used, and none is available to paper over a gap.

Consequence, and this is the single most useful thing this scout returns: if any
of the twelve clauses is genuinely undecidable, then **no total `check`
satisfying both rows exists**. `T011` is then FALSE, not open. -/

section Decision

variable {Raw Diag Checked : Type}

/-- `EC1-T010` schematically. The `Sigma CheckedProgram` payload is abstracted
to a single `Checked`, because `T010`'s conclusion never mentions it. -/
def Sound (P : Raw → Prop) (chk : Raw → Except Diag Checked) : Prop :=
  ∀ r c, chk r = .ok c → P r

/-- `EC1-T011` schematically, with the AER existential restored.

**Statement defect in the DAG row.** `PROOF-DAG.md:213` writes
`check_complete : ProgramWF r -> exists p, check r = ok <a,p>` with `a` free.
Read with `a` universally quantified outside, the row claims a well-formed
program checks at EVERY `aer`, which is false as soon as `AER` has two
inhabitants. The binder must be `∃ a p`, matching `check`'s own
`Except Diagnostic (Sigma CheckedProgram)` codomain. -/
def Complete (P : Raw → Prop) (chk : Raw → Except Diag Checked) : Prop :=
  ∀ r, P r → ∃ c, chk r = .ok c

/-- **The construction.** A sound and complete total checker IS a decision
procedure for the property it checks. Constructive: `Except`'s two arms are the
excluded middle here, supplied by the checker's own totality. -/
def decideOfCheck {P : Raw → Prop} {chk : Raw → Except Diag Checked}
    (hs : Sound P chk) (hc : Complete P chk) (r : Raw) : Decidable (P r) :=
  match h : chk r with
  | .ok c => isTrue (hs r c h)
  | .error _ =>
      isFalse fun hp => by
        obtain ⟨_, hok⟩ := hc r hp
        rw [h] at hok
        exact absurd hok (by simp)

/-- Packaged as the pointwise decision the checker family would have to supply.
Spelled out rather than as `DecidablePred` so this stays plain data. -/
def decideAll {P : Raw → Prop} {chk : Raw → Except Diag Checked}
    (hs : Sound P chk) (hc : Complete P chk) : ∀ r, Decidable (P r) :=
  decideOfCheck hs hc

/-- The contrapositive, stated so it cannot be read as advice. If `P` at some
input admits no decision, no total checker satisfies both `EC1-T010` and
`EC1-T011` for it. -/
theorem no_sound_complete_checker_of_undecidable {P : Raw → Prop} {r : Raw}
    (hu : Decidable (P r) → False) (chk : Raw → Except Diag Checked)
    (hs : Sound P chk) (hc : Complete P chk) : False :=
  hu (decideOfCheck hs hc r)

/-! ### §2b — where a semantic clause actually breaks

§2 says an undecidable clause makes `T011` false. The realistic failure is
softer and worth naming separately, because it is what four of the twelve
clauses invite.

Three clauses are written with a semantic word next to a syntactic one:

* clause 3 `RowsWF` — "every ESCAPED typed failure is in `E`";
* clause 5 `HandlersWF` — "every REACHABLE operation";
* clause 8 `ResourcesWF` — resource tokens "cannot ESCAPE their scope".

A real checker decides the SYNTACTIC over-approximation `S` (graph reachability,
syntactic occurrence), which strictly implies the semantic reading `P`. The pair
of theorems below is the consequence, and the asymmetry is the finding:
soundness survives the substitution and completeness dies at the first program
that is semantically fine and syntactically condemned. Combined with §2, that
failure is not repairable by a better checker. -/

/-- Deciding a STRONGER clause keeps `EC1-T010`. -/
theorem strengthening_preserves_sound {P S : Raw → Prop}
    {chk : Raw → Except Diag Checked} (hSP : ∀ r, S r → P r)
    (hs : Sound S chk) : Sound P chk :=
  fun r c h => hSP r (hs r c h)

/-- And kills `EC1-T011` outright at any witness the strengthening separates:
one program that is semantically well formed and syntactically condemned refutes
completeness for the semantic reading. There is no third option, because §2
already ruled out an oracle. -/
theorem strict_strengthening_kills_complete {P S : Raw → Prop}
    {chk : Raw → Except Diag Checked} (hsS : Sound S chk)
    (r : Raw) (_hp : P r) (hns : ¬ S r) : ¬ Complete P chk := by
  intro hc
  obtain ⟨c, hok⟩ := hc r _hp
  exact hns (hsS r c hok)

end Decision

/-! ## §3 — `EC1-T012` is free, and its stated dependency is redundant

`PROOF-DAG.md:214` gives `EC1-T012` the dependency `T010,T011; decidable WF`.
The third item is not needed. The two-arm case split on `chk r` already supplies
everything, and the derivation below uses no `Decidable` premise and no
classical axiom.

This is not a weakening. It is the observation that `T010 ∧ T011` ALREADY
implies decidability (§2), so listing decidability again as a `T012` premise
double-counts one obligation. -/

section ErrorIff

variable {Raw Diag Checked : Type}

/-- `EC1-T012 check_error_iff`, derived. No decidability premise. -/
theorem error_iff_of_sound_complete {P : Raw → Prop}
    {chk : Raw → Except Diag Checked}
    (hs : Sound P chk) (hc : Complete P chk) (r : Raw) :
    (∃ d, chk r = .error d) ↔ ¬ P r := by
  constructor
  · rintro ⟨d, hd⟩ hp
    obtain ⟨c, hok⟩ := hc r hp
    rw [hd] at hok
    exact absurd hok (by simp)
  · intro hnp
    match h : chk r with
    | .ok c => exact absurd (hs r c h) hnp
    | .error d => exact ⟨d, rfl⟩

end ErrorIff

/-! ## §4 — the order obligation: check the RAW, then normalize

`EC1-T010`'s conclusion is `ProgramWF r` — a statement about the checker's RAW
input. `EC1-K10` (`CONTRACT-PACKET.md:306-310`) separately requires
`erase checked = normalizeRaw (erase checked)`. Read together, those two invite
a checker that normalizes first and checks the normal form. That checker cannot
prove `T010`.

The reason is `EC1-CE030`/`R16` part 2, landing one row earlier than the register
files it. Normalization does not merely PRESERVE the duplicate-free clause — it
CREATES it. So the implication `ProgramWF (normalizeRaw r) → ProgramWF r` runs
the wrong way through clause 1 (`IdsWF`, "every table is duplicate-free").

Proved below at the estate's one shipped keyed-row normalizer rather than at a
toy, so the witness is against live code. -/

section OrderObligation

open Cas.Backend Cas.Schema

/-- `IdsWF`'s duplicate-free conjunct at the estate's shipped keyed-row carrier
(`ALGEBRA.md:296`, clause 1). -/
def NodupKeys (xs : List ServiceRef) : Prop := (xs.map (·.key)).Nodup

/-- Normalization ALWAYS establishes the clause — `Cas/Backend/Canon.lean:167`.
The normal form is duplicate-free whatever the input was. -/
theorem norm_always_nodup (xs : List ServiceRef) :
    NodupKeys (canonServices xs) :=
  nodup_keys_canonServices xs

private def dupL : ServiceRef := { key := "k", name := "L", path := "l" }
private def dupR : ServiceRef := { key := "k", name := "R", path := "r" }

/-- Two rows, one key: the raw table that fails clause 1. -/
private def dupTable : List ServiceRef := [dupL, dupR]

theorem dupTable_not_nodup : ¬ NodupKeys dupTable := by
  simp [NodupKeys, dupTable, dupL, dupR]

/-- **The order obligation.** There is a raw table whose NORMAL FORM satisfies
the duplicate-free clause while the raw table itself does not. Hence
`ProgramWF (normalizeRaw r) → ProgramWF r` is false, and a checker that
normalizes before it checks proves nothing about `r`.

`EC1-T010` therefore forces a checker ORDER: decide every clause on the raw
input, and normalize only inside the `CheckedProgram` payload afterwards. -/
theorem normalize_then_check_cannot_prove_T010 :
    ∃ xs : List ServiceRef, NodupKeys (canonServices xs) ∧ ¬ NodupKeys xs :=
  ⟨dupTable, norm_always_nodup dupTable, dupTable_not_nodup⟩

/-- The positive boundary, so the finding is not read as an attack on
normalization: on a table that already satisfies the clause, normalization is a
reordering and nothing else (`Cas/Backend/Canon.lean:288`). The raw judgment and
the normal-form judgment coincide exactly where clause 1 already holds. -/
theorem normalization_is_harmless_where_the_clause_holds
    {xs : List ServiceRef} (h : NodupKeys xs) : (canonServices xs).Perm xs :=
  canonServices_perm_of_nodup_keys h

end OrderObligation

/-! ## §5 — `EC1-T016` is vacuous as written

```
EC1-T016  aer_synthesis_unique : ProgramWF r -> exists! aer, SynthAER r aer
```

`ALGEBRA.md:296` clause 11 (`AERWF`) says the synthesized triple "normalizes to
the declared triple". That phrasing makes `SynthAER` a FUNCTION composed with a
normalizer, and `SynthAER r aer` its graph. `∃!` over a function's graph is a
tautology.

Two theorems below. The first is `T016`'s exact shape with the premise still in
place, proved WITHOUT USING IT — which is the sharp form of the vacuity charge,
since a proof that never touches `ProgramWF r` cannot be said to depend on
admission. The second exhibits the shape that would carry content. -/

section AerVacuity

/-- **`EC1-T016`, vacuous.** `Q` stands for `ProgramWF` and `f` for the
synthesizer. The hypothesis is bound and never used; `∃!` collapses to `rfl`. -/
theorem existsUnique_over_a_function_graph_is_vacuous
    {α β : Type} (Q : α → Prop) (f : α → β) (r : α) (_hq : Q r) :
    ∃ b, f r = b ∧ ∀ b', f r = b' → b' = b :=
  ⟨f r, rfl, fun _ h => h.symm⟩

/-- The premise really is dead: the same statement holds at the FALSE premise,
so `T016` distinguishes no admitted program from any other. -/
theorem existsUnique_holds_even_at_False
    {α β : Type} (f : α → β) (r : α) :
    ∃ b, f r = b ∧ ∀ b', f r = b' → b' = b :=
  ⟨f r, rfl, fun _ h => h.symm⟩

/-- The non-vacuous replacement, in the estate's own idiom
(`Cas/Schema/Declarations.lean:288/297`, `Cas/Backend/Canon.lean:259/278/288`):
uniqueness of the SYNTHESIZER under named laws, not uniqueness of a value in its
graph. Here the law is agreement with a declared triple on admitted inputs;
two synthesizers satisfying it are equal there.

This is a schema, not a result about a `SynthAER` that does not yet exist: it
records the shape `T016` must take to say anything. -/
theorem synthesizer_pinned_by_its_law
    {α β : Type} {Q : α → Prop} {declared : α → β} (f g : α → β)
    (hf : ∀ r, Q r → f r = declared r) (hg : ∀ r, Q r → g r = declared r)
    (r : α) (hr : Q r) : f r = g r := by
  rw [hf r hr, hg r hr]

end AerVacuity

/-! ## §6 — first-error composition: what §16's route actually buys

`PROOF-DAG.md` §16 names the Checker route: "structural recursion plus decidable
per-clause reflection". At twelve clauses composed by `Except` short-circuit,
those two words behave asymmetrically, and the asymmetry is exactly `R16`.

SOUNDNESS composes for free: an `ok` from a short-circuiting sequence means
every clause returned `ok`, so each clause's own soundness fires and the
conclusion is the CONJUNCTION. That is `T010` at twelve clauses, and it costs one
lemma per clause.

COMPLETENESS does not compose for free: it needs every clause complete AND every
clause decided against the SAME raw value (§4). The lemma below is the
composable half; its absence of a dual is the point. -/

section Composition

variable {Raw Diag : Type}

/-- Soundness composes over first-error sequencing, at the conjunction. -/
theorem sound_seq {P Q : Raw → Prop} (f g : Raw → Except Diag Unit)
    (hf : ∀ r, f r = .ok () → P r) (hg : ∀ r, g r = .ok () → Q r)
    (r : Raw) (h : (f r).bind (fun _ => g r) = .ok ()) : P r ∧ Q r := by
  match hfr : f r with
  | .ok u =>
      cases u
      rw [hfr] at h
      exact ⟨hf r hfr, hg r h⟩
  | .error d =>
      rw [hfr] at h
      exact absurd h (by simp [Except.bind])

/-- And the first-error discipline the composition inherits: an error from the
sequence is one clause's error, never a set of them. `EC1-CE031` already proved
the estate's checker reports only the first; this is the same fact at the
abstract composition, which is where the twelve-clause checker will live. -/
theorem seq_error_is_one_clause {f g : Raw → Except Diag Unit} {r : Raw}
    {d : Diag} (h : (f r).bind (fun _ => g r) = .error d) :
    f r = .error d ∨ (∃ u, f r = .ok u) ∧ g r = .error d := by
  match hfr : f r with
  | .ok u => exact Or.inr ⟨⟨u, rfl⟩, by rw [hfr] at h; exact h⟩
  | .error d' => rw [hfr] at h; exact Or.inl (by rw [← Except.error.inj h])

end Composition

end EffectCoreScoutT010

/-! ## Kernel receipts

Every theorem and every construction above. `decideOfCheck`/`decidableOfCheck`
are data, and their axiom sets are printed for the same reason: a decision
procedure that leaned on choice would not be a decision procedure. -/

#print axioms EffectCoreScoutT010.anchor_T010
#print axioms EffectCoreScoutT010.anchor_T011
#print axioms EffectCoreScoutT010.anchor_first_error
#print axioms EffectCoreScoutT010.decideOfCheck
#print axioms EffectCoreScoutT010.decideAll
#print axioms EffectCoreScoutT010.no_sound_complete_checker_of_undecidable
#print axioms EffectCoreScoutT010.strengthening_preserves_sound
#print axioms EffectCoreScoutT010.strict_strengthening_kills_complete
#print axioms EffectCoreScoutT010.error_iff_of_sound_complete
#print axioms EffectCoreScoutT010.norm_always_nodup
#print axioms EffectCoreScoutT010.dupTable_not_nodup
#print axioms EffectCoreScoutT010.normalize_then_check_cannot_prove_T010
#print axioms EffectCoreScoutT010.normalization_is_harmless_where_the_clause_holds
#print axioms EffectCoreScoutT010.existsUnique_over_a_function_graph_is_vacuous
#print axioms EffectCoreScoutT010.existsUnique_holds_even_at_False
#print axioms EffectCoreScoutT010.synthesizer_pinned_by_its_law
#print axioms EffectCoreScoutT010.sound_seq
#print axioms EffectCoreScoutT010.seq_error_is_one_clause
