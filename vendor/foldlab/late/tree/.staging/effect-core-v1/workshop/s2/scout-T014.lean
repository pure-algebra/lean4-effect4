import Cas.Core.Admission
import Cas.Backend.Canon
import Cas.Lang.Defun
import Cas.Lift.Decode

/-!
# Effect Core v1 — forward scout probe for `EC1-T014` (slice `EC1-S2`)

Row under scout: `EC1-T014 erase_wf : ProgramWF (erase p)`
(`PROOF-DAG.md:216`, depends on `T010,T013`).
Target module, NOT written here: `formal/effect-core-v1/EffectCore/Admission/Check.lean`.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/scout-T014.lean
```

## Why this file is a MODEL and not the theorem

`EC1-D020 RawProgram`, `EC1-D021 ProgramWF`, `EC1-D023 CheckedProgram`,
`EC1-D024 check` and `EC1-D025 erase` are all `PROPOSED TERM` in
`PROOF-DAG.md:107-113`. None of them has a Lean definition anywhere in this
tree (`formal/effect-core-v1/EffectCore/Admission/Check.lean` is an empty
reserved boundary). So `EC1-T014` cannot be stated yet, let alone proved.

What CAN be settled before the carrier exists is which of the competing
carrier designs makes `erase_wf` a theorem at all, and which `ProgramWF`
clauses admit a decision procedure. That is what the five sections below do.
Sections 1 and 6 run against the estate's real carriers; sections 2-5 are
explicitly abstract models whose only job is to separate designs.

A successful elaboration below proves the stated proposition and nothing more.
It closes no proof-DAG row and gives no assurance about any future checker.

| § | Question | Finding |
|---|---|---|
| 1 | Is "decidable per-clause reflection" real at the estate's carrier? | Yes; built by structural recursion, decides positives and negatives. |
| 2 | Is `∃!` over a Lean function vacuous (bears on `EC1-T016`)? | Yes, and the `ProgramWF` premise is provably dead. |
| 3 | Design (a): `CheckedProgram` bundles `ProgramWF`. | `erase_wf` is the `wf` FIELD. No checker, no `T010`, no `T013`. |
| 4 | Design (b): `erase` normalizes. | `erase_wf` is FALSE without a normalizer-preservation premise. |
| 5 | Is `ProgramWF` a predicate on `RawProgram` alone? | No. Clauses 5 and 9 are environment-relative; `EC1-D021` drops the index. |
| 6 | Do the reported anchors resolve? | Yes — all six re-elaborated here. |
-/

namespace ScoutT014

/-! ## §1 — decidable per-clause reflection, at the estate's real carrier

`PROOF-DAG.md:518` fixes the Checker family's route: "structural recursion plus
decidable per-clause reflection". The estate already runs that route twice:
`Cas/Core/Node.lean:47-51` pairs `Node.WF` with an explicit `Decidable`
instance, and `Cas/Lang/Defun.lean:191` defines `PLine.WF` by pattern match into
decidable atoms. `PLine.WF` ships WITHOUT a decidability instance, so the route
is asserted for it rather than exhibited. This section exhibits it.

Instances are written as recursive TERMS, not by tactic, so they reduce in the
kernel and `decide` can actually run them. -/

section Reflection

open Cas.Lang

/-- Clause reflection at the operand level (`Cas/Lang/Defun.lean:172`). -/
instance decPInWF : ∀ i : PIn, Decidable i.WF
  | .lit _ => .isTrue trivial
  | .ans i => inferInstanceAs (Decidable (i < 4294967296))

/-- Clause reflection at the code-point level (`Cas/Lang/Defun.lean:191`).
Three conjuncts, one of them a bounded quantifier over a list — exactly the
shape every `ProgramWF` clause is proposed to have. -/
instance decPLineWF : ∀ l : PLine, Decidable l.WF
  | .put _ _ payload refs =>
      inferInstanceAs
        (Decidable (payload.length < 4294967296 ∧ refs.length < 4294967296 ∧
          ∀ r ∈ refs, r.2.WF))
  | .load src => decPInWF src

/-- The table-level judgment: the estate's own spelling of "this program is
well-formed" is a bounded quantifier over the code-point table. This is the
`ProgramWF` shape one level down. -/
def TableWF (p : PProg) : Prop := ∀ l ∈ p, l.WF

instance decTableWF : DecidablePred TableWF :=
  fun p => List.decidableBAll _ p

/-- POSITIVE: the checker accepts. -/
theorem tableWF_decides_accept :
    decide (TableWF [PLine.load (.ans 0), PLine.put 0 7 [] []]) = true := by
  decide

/-- NEGATIVE: the checker rejects, and it rejects by COMPUTATION rather than by
absence of a positive example. `PROOF-DAG.md:518` names "using successful
examples as completeness" as the prohibited shortcut for this family; a
reduction to `false` is not that shortcut. -/
theorem tableWF_decides_reject :
    decide (TableWF [PLine.load (.ans 4294967296)]) = false := by
  decide

/-- The rejection is a real refutation of the judgment, not merely a `false`
Boolean: the two are tied by the instance. -/
theorem tableWF_reject_is_a_refutation :
    ¬ TableWF [PLine.load (.ans 4294967296)] :=
  of_decide_eq_false tableWF_decides_reject

end Reflection

/-! ## §2 — `∃!` over a Lean function is a tautology (bears on `EC1-T016`)

`EC1-T016 aer_synthesis_unique : ProgramWF r -> exists! aer, SynthAER r aer`
(`PROOF-DAG.md:218`). `PROOF-DAG.md:203-205` already deleted two rows in this
packet for exactly this defect. The row survives only if `SynthAER` is a
genuine RELATION. If it is a function and `SynthAER r aer` abbreviates
`SynthAER r = aer`, the row is a tautology and the `ProgramWF r` premise is
dead weight.

Three further rows have the same shape, and two of them are the rows that would
discharge the `ProgramWF` clauses this slice depends on:

* `PROOF-DAG.md:306` `EC1-T050 direct_lookup_unique : HandlerEnvWF h ->
  reachable op -> exists! clause, directLookup h op = clause` — the `HandlersWF`
  (clause 5) row;
* `PROOF-DAG.md:392` `EC1-T090 foreign_registry_total : ForeignWF p ->
  reachable foreignOp -> exists! entry, registryLookup = entry` — the
  `ForeignWF` (clause 9) row;
* `PROOF-DAG.md:200` `EC1-T008 surface_disposition_total : PublicSurfaceWF s ->
  forall row in s, exists! d, disposition row = d`.

`PROOF-DAG.md:196` `EC1-T004 alphabet_lookup_total : op in a -> exists! d,
lookup a op = some d` is only HALF vacuous: uniqueness is free by injectivity of
`some`, existence is real content. -/

section Vacuity

/-- `exists!` written out. The estate's Lean environment has NO Mathlib and no
`ExistsUnique`: both `∃!` and the bare constant fail to elaborate under
`library/cas`'s toolchain (`leanprover/lean4:v4.33.1`, `lakefile.toml` requires
nothing). So `EC1-T004`, `EC1-T008` and `EC1-T016` cannot be written in the
packet's own spelling without a new dependency — and written out, the defect is
unmissable. -/
def ExistsUniq {β : Type} (P : β → Prop) : Prop :=
  ∃ y, P y ∧ ∀ z, P z → z = y

/-- The tautology, for every function and every argument. No premise. -/
theorem exists_unique_of_a_function :
    ∀ {α β : Type} (f : α → β) (x : α), ExistsUniq (fun y => f x = y) :=
  fun f x => ⟨f x, rfl, fun _ h => h.symm⟩

/-- The `EC1-T016` shape holds for EVERY predicate `P` in the premise slot —
including one no program satisfies and one every program satisfies. A premise
that can be replaced by `fun _ => True` without touching the proof is doing no
work. -/
theorem t016_premise_is_dead :
    ∀ {α β : Type} (f : α → β) (P : α → Prop) (x : α),
      P x → ExistsUniq (fun y => f x = y) :=
  fun f _ x _ => exists_unique_of_a_function f x

/-- Stated the other way round, so the deadness is unmissable: the premise-free
statement is strictly stronger and already true. -/
theorem t016_holds_without_any_premise :
    ∀ {α β : Type} (f : α → β) (x : α), ExistsUniq (fun y => f x = y) :=
  exists_unique_of_a_function

/-- The contrast that makes the row worth keeping. For a genuine relation,
uniqueness is a real obligation: this relation over-derives. -/
theorem relational_synthesis_can_over_derive :
    ¬ ExistsUniq (fun y : Nat => (fun (_ _ : Nat) => True) 0 y) :=
  fun hx => Exists.elim hx fun _ hy =>
    absurd ((hy.2 0 trivial).trans (hy.2 1 trivial).symm) (by decide)

/-- And existence is a real obligation: this relation under-derives. -/
theorem relational_synthesis_can_under_derive :
    ¬ ExistsUniq (fun y : Nat => (fun (_ _ : Nat) => False) 0 y) :=
  fun hx => Exists.elim hx fun _ hy => hy.1

end Vacuity

/-! ## §3 — design (a): `CheckedProgram` bundles the `ProgramWF` evidence

`ALGEBRA.md:319-320`: "`EC1-A13 CheckedProgram A E R` stores an erased raw value,
normalized lookup tables, and evidence of `ProgramWF`."

Take that sentence literally and `erase_wf` stops being a theorem: it is the
`wf` projection. The model below is deliberately maximally general — `WF` is an
ARBITRARY predicate, possibly undecidable, with no checker in sight. -/

section Bundled

/-- The carrier `ALGEBRA.md:319-320` describes. -/
structure Checked (Raw : Type) (WF : Raw → Prop) where
  raw : Raw
  wf : WF raw

/-- `EC1-D025 erase` in design (a). -/
def eraseBundled {Raw : Type} {WF : Raw → Prop} (p : Checked Raw WF) : Raw := p.raw

/-- **`EC1-T014` in design (a).** The statement holds for every predicate, with
no checker, no soundness theorem, and no round trip — so its DAG dependencies
`T010,T013` are not merely unnecessary, they are unmentionable: nothing in this
statement can refer to a checker. -/
theorem erase_wf_bundled :
    ∀ {Raw : Type} {WF : Raw → Prop} (p : Checked Raw WF), WF (eraseBundled p) :=
  fun p => p.wf

/-- The proof term IS the field selector. This is what "vacuous by
construction" means here — not that the statement is trivially true (a `WF`
nobody can satisfy makes `Checked` uninhabited), but that it carries no
information beyond the definition of the carrier. -/
theorem erase_wf_bundled_is_the_field_selector :
    @erase_wf_bundled = fun _ _ p => Checked.wf p := rfl

end Bundled

/-! ## §4 — design (b): `erase` normalizes, and then `EC1-T014` is FALSE

`CONTRACT-PACKET.md:309` requires `erase checked = normalizeRaw (erase checked)`
— erase lands on a `normalizeRaw` fixed point. There are two ways to satisfy
that, and they give `EC1-T014` opposite contents:

* store an already-normalized raw and project (design (a), §3); or
* store an arbitrary admitted raw and normalize on the way out (design (b)).

In design (b) `EC1-T014` unfolds to `ProgramWF r -> ProgramWF (normalizeRaw r)`,
which is an INDEPENDENT obligation the packet does not currently own. It is not
implied by `T010`, `T013`, `T006` (idempotence, `PROOF-DAG.md:198`) or `T007`.

The model below proves independence: a well-formedness predicate and a
deduplicating normalizer where preservation fails. The shape is not invented —
`Cas/Backend/Canon.lean:376` `canonServices_perm_premise_is_necessary` is the
estate's own witness that its shipped normalizer COLLAPSES duplicate keys, and
`EC1-CE030` is the register row that forced a `Nodup` premise onto `EC1-T002`
for exactly that reason. -/

section Normalized

/-- A multiplicity-sensitive well-formedness clause. `RowsWF`, `IdsWF` and
`EntryWF` (`ALGEBRA.md:297-318`) all count table entries. -/
def CountsTwo (r : List Nat) : Prop := r.length = 2

/-- A deduplicating normalizer, written in exactly the shape of the estate's
own `canonDedup` (`Cas/Backend/Canon.lean:109`) so it reduces in the kernel. -/
def normalizeDedup : List Nat → List Nat
  | [] => []
  | a :: rest =>
    let t := normalizeDedup rest
    if t.contains a then t else a :: t

theorem dedup_collapses_a_duplicate : normalizeDedup [1, 1] = [1] := by decide

/-- **`EC1-T014` in design (b) is false without a preservation premise.** -/
theorem erase_wf_normalized_is_false :
    ¬ ∀ r : List Nat, CountsTwo r → CountsTwo (normalizeDedup r) := by
  intro h
  have hlen : (normalizeDedup [1, 1]).length = 2 := h [1, 1] rfl
  rw [dedup_collapses_a_duplicate] at hlen
  exact absurd hlen (by decide)

/-- The missing lemma, named. Design (b) owes this and the packet has no row
for it; `T006` gives idempotence of the normalizer, not preservation of `WF`. -/
def NormalizerPreservesWF (WF : List Nat → Prop) (norm : List Nat → List Nat) : Prop :=
  ∀ r, WF r → WF (norm r)

theorem the_owed_premise_is_exactly_this :
    ¬ NormalizerPreservesWF CountsTwo normalizeDedup :=
  erase_wf_normalized_is_false

end Normalized

/-! ## §5 — `ProgramWF` is environment-relative; `EC1-D021` drops the index

The estate's admission judgment is EXPLICITLY environment-indexed:

```text
Cas/Core/Admission.lean:49  checkRefs (σ : Store) : List Ref → Except AdmissionError Unit
Cas/Core/Admission.lean:60  checkRefs_ok_iff {σ : Store} {rs : List Ref} :
                              checkRefs σ rs = .ok () ↔ RefsOk σ rs
```

The proposed one is not:

```text
PROOF-DAG.md:108  ProgramWF : RawProgram -> Prop
PROOF-DAG.md:111  check : RawProgram -> Except Diagnostic (Sigma CheckedProgram)
```

Two `ProgramWF` clauses need an object the raw program does not carry.
`ALGEBRA.md:312` `ForeignWF` — "every foreign ID resolves to a REGISTRY ENTRY
whose types, frame, receipt codec, and observation class are present" — needs
the registry; `ALGEBRA.md:298` `TypesWF` needs the `Alphabet`, which
`ALGEBRA.md:131` makes separate versioned CONTENT, hence resolved through a
store exactly as `checkRefs` resolves a `Ref`. (`HandlersWF`, clause 5, may be
self-contained: `REIFICATION-CHECKLIST.md:857-858` lists a handler table inside
`RawProgram`. That is a design decision the packet has not recorded either way.)

`.staging/agent-reports/2026-08-31-effect-core-local-anchors.md:276` records the
same observation for `T010` and calls it a WIDENING: "the judgment goes from
store-relative to program-relative". Dropping the index is not a widening. The
theorems below show it changes what the proposition can assert. -/

section EnvironmentRelative

/-- A registry: the foreign IDs that resolve. -/
abbrev Registry := List Nat

/-- `ForeignWF`, honestly indexed. -/
def ForeignWF (ρ : Registry) (r : List Nat) : Prop := ∀ i ∈ r, i ∈ ρ

instance decForeignWF (ρ : Registry) : DecidablePred (ForeignWF ρ) :=
  fun r => List.decidableBAll _ r

/-- **The obstruction.** The same raw program is well-formed against one
registry and ill-formed against another. So `ProgramWF r` alone denotes nothing
until the environment is fixed, and `EC1-T014` must read
`ProgramWF ρ (erase p)` for the `ρ` that `p` was checked against. -/
theorem programWF_is_registry_relative :
    ∃ (ρ ρ' : Registry) (r : List Nat), ForeignWF ρ r ∧ ¬ ForeignWF ρ' r :=
  ⟨[1], [], [1], by decide, by decide⟩

/-- The repaired carrier: the `CheckedProgram` must PIN the registry it was
admitted against, otherwise the `wf` field has no subject. With the pin,
`erase_wf` recovers — at the pinned registry only. -/
structure CheckedAt (WF : Registry → List Nat → Prop) where
  reg : Registry
  raw : List Nat
  wf : WF reg raw

theorem erase_wf_at_the_pinned_registry :
    ∀ {WF : Registry → List Nat → Prop} (p : CheckedAt WF), WF p.reg p.raw :=
  fun p => p.wf

/-- And it does NOT recover at any other registry — the quantifier the DAG
signature suppresses is load-bearing. -/
theorem erase_wf_does_not_generalize_over_registries :
    ¬ ∀ (p : CheckedAt ForeignWF) (ρ : Registry), ForeignWF ρ p.raw := by
  intro h
  exact absurd (h ⟨[1], [1], by decide⟩ []) (by decide)

end EnvironmentRelative

/-! ## §6 — anchor re-elaboration

Every anchor the local-anchor lane reported for this neighbourhood, named at its
reported `file:line` and forced through the elaborator. A name that did not
resolve would fail this file. -/

section Anchors

/-- `T014` anchor, `Cas/Lift/Decode.lean:422`: the door answers only well-formed
lines. The `EC1-T014` statement one level down — and note its shape is
`decodeLift v = .ok l → (well-formedness of l)`, i.e. it is SOUNDNESS OF THE
DOOR, obtained from the door's own recursion, not from a round trip. -/
abbrev anchor_T014 := @Cas.Lift.decodeLift_wf

/-- `T010` anchor, `Cas/Core/Admission.lean:60`. -/
abbrev anchor_T010 := @Cas.checkRefs_ok_iff

/-- `T010`/`T015` anchor, `Cas/Core/Admission.lean:108`. -/
abbrev anchor_T010b := @Cas.checkRefs_error_condemns

/-- `T011` anchor, `Cas/Core/Admission.lean:137` — existential in the error,
which is `R16`'s existential rejection completeness, already shipped. -/
abbrev anchor_T011 := @Cas.checkRefs_complete

/-- `T013` anchor, `Cas/Lang/Defun.lean:998` — the estate's only erase/recover
round trip, and it carries TWO premises. -/
abbrev anchor_T013 := @Cas.Lang.decodeProg_encodeProg

/-- `EC1-CE030` / `R16` part 2, `Cas/Backend/Canon.lean:288` and `:376`. The
positive needs `Nodup`; the premise-free form is refuted. -/
abbrev anchor_CE030_positive := @Cas.Backend.canonServices_perm_of_nodup_keys
abbrev anchor_CE030_negative := @Cas.Backend.canonServices_perm_premise_is_necessary

end Anchors

end ScoutT014

/-! ## Kernel receipts -/

#print axioms ScoutT014.tableWF_decides_accept
#print axioms ScoutT014.tableWF_decides_reject
#print axioms ScoutT014.tableWF_reject_is_a_refutation
#print axioms ScoutT014.exists_unique_of_a_function
#print axioms ScoutT014.t016_premise_is_dead
#print axioms ScoutT014.t016_holds_without_any_premise
#print axioms ScoutT014.relational_synthesis_can_over_derive
#print axioms ScoutT014.relational_synthesis_can_under_derive
#print axioms ScoutT014.erase_wf_bundled
#print axioms ScoutT014.erase_wf_bundled_is_the_field_selector
#print axioms ScoutT014.dedup_collapses_a_duplicate
#print axioms ScoutT014.erase_wf_normalized_is_false
#print axioms ScoutT014.the_owed_premise_is_exactly_this
#print axioms ScoutT014.programWF_is_registry_relative
#print axioms ScoutT014.erase_wf_at_the_pinned_registry
#print axioms ScoutT014.erase_wf_does_not_generalize_over_registries
#print axioms ScoutT014.anchor_T014
#print axioms ScoutT014.anchor_T010
#print axioms ScoutT014.anchor_T010b
#print axioms ScoutT014.anchor_T011
#print axioms ScoutT014.anchor_T013
#print axioms ScoutT014.anchor_CE030_positive
#print axioms ScoutT014.anchor_CE030_negative
