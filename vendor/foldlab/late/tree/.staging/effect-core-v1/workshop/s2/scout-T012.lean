import Cas.Core.Admission
import Cas.IR.Reach

/-!
# Effect Core v1 — forward scout probe for `EC1-T012`

Row under scout (`PROOF-DAG.md:214`):

```text
EC1-T012  check_error_iff : (exists d, check r = error d) <-> not ProgramWF r
          depends on: T010, T011; decidable WF
```

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/scout-T012.lean
```

SCOUTING ONLY. Nothing here is proposed for `library/` or for
`formal/effect-core-v1/`. Every theorem below is a statement about an
ABSTRACT checker `check : R -> Except D C` and an abstract predicate
`WF : R -> Prop`, plus one instantiation at the estate's shipped
`Cas.checkRefs`. None of it constructs Effect Core's `check`, `ProgramWF`,
`RawProgram`, `Diagnostic`, or `SynthAER`, and none of it closes `EC1-T012`.

What the sections settle:

| § | Question | Finding |
|---|---|---|
| 1 | Does `T012` need `decidable WF`? | NO. It is a pure `Except`-sum corollary of `T010 + T011`. |
| 2 | Where does decidability live? | It is DERIVED from `T010 + T011`, not assumed. |
| 3 | Is either direction redundant? | NO. Each direction is exactly one of the two contrapositives; two independence witnesses. |
| 4 | Is "decidable per-clause reflection" (`PROOF-DAG.md:518`) enough? | NO. The estate's own reachability decision is PREMISE-CARRYING; clauses must be staged. |
| 5 | Can the DAG's decidability prohibition be enforced by elaboration? | NO. `Classical` inhabits `Decidable p` for every `p`. The only kernel-visible gate is the AXIOM RECEIPT on `T011`. |
| 6 | Is the `exists!` vacuity pattern live for the AER clause? | The premise is provably inert IF the relation is a function graph. `SynthAER` has no defining term to check. |
| 7 | Does the anchor actually carry `T012`'s shape? | YES — `checkRefs_ok_iff` alone yields the row's exact form and its `Decidable`. |

Axiom discipline: `#print axioms` on every theorem at the foot. No `sorry`,
no `axiom`, no `native_decide`, no `#eval` standing in for a claim.
-/

namespace EffectCoreScoutT012

/-! ## §1 — `T012` is a corollary of `T010 + T011`, with NO decidability premise

The row's stated dependency list is `T010, T011; decidable WF`. The third
entry is not needed for the STATEMENT. `Except` is a two-constructor disjoint
sum, so case analysis on `check r` plus the two adequacy directions closes the
iff outright, at any types whatsoever.

This is deliberately stated at maximal generality — `R`, `D`, `C` arbitrary,
`WF` an arbitrary `Prop`-valued predicate, no `Decidable` anywhere in scope —
so that no instance can be silently doing work. -/

section Corollary

variable {R D C : Type} (check : R → Except D C) (WF : R → Prop)

/-- `T010` in abstract form: what the checker accepts is well formed. -/
abbrev Sound : Prop := ∀ r c, check r = .ok c → WF r

/-- `T011` in abstract form: a well-formed input is accepted. Existential in
the certificate, matching `PROOF-DAG.md:213`. -/
abbrev Complete : Prop := ∀ r, WF r → ∃ c, check r = .ok c

/-- **FINDING 1.** `EC1-T012` follows from `EC1-T010` and `EC1-T011` alone.
No decidability hypothesis appears, and none is used. -/
theorem check_error_iff_of_sound_complete
    (hs : Sound check WF) (hc : Complete check WF) (r : R) :
    (∃ d, check r = .error d) ↔ ¬ WF r := by
  constructor
  · rintro ⟨d, hd⟩ hwf
    obtain ⟨c, hcc⟩ := hc r hwf
    rw [hd] at hcc
    exact nomatch hcc
  · intro hnwf
    cases h : check r with
    | ok c => exact absurd (hs r c h) hnwf
    | error d => exact ⟨d, rfl⟩

/-- The forward half in isolation: it is exactly `T011`'s contrapositive. -/
theorem error_imp_not_wf (hc : Complete check WF) (r : R) :
    (∃ d, check r = .error d) → ¬ WF r := by
  rintro ⟨d, hd⟩ hwf
  obtain ⟨c, hcc⟩ := hc r hwf
  rw [hd] at hcc
  exact nomatch hcc

/-- The backward half in isolation: it is exactly `T010`'s contrapositive,
plus totality of the sum. -/
theorem not_wf_imp_error (hs : Sound check WF) (r : R) :
    ¬ WF r → ∃ d, check r = .error d := by
  intro hnwf
  cases h : check r with
  | ok c => exact absurd (hs r c h) hnwf
  | error d => exact ⟨d, rfl⟩

end Corollary

/-! ## §2 — decidability is a CONSEQUENCE of the pair, not a premise

`PROOF-DAG.md:214` lists `decidable WF` as a dependency of `T012`. That is
backwards. `T010 + T011` together already CONSTRUCT the decision procedure:
the checker itself is it. The decidability burden is entirely inside the
PROOF of `T011` (you must exhibit a checker that succeeds on every well-formed
input), never in `T012`'s statement or dependencies.

Note the instance below is `def`, not `instance`, and it takes the two
adequacy proofs as explicit arguments — the same honesty the estate applies to
`Cas.Word.decidableReach` (`Cas/IR/Reach.lean:551`), which "carries NO
`instance` attribute, on purpose". -/

section Derived

variable {R D C : Type} (check : R → Except D C) (WF : R → Prop)

set_option warn.classDefReducibility false in
/-- **FINDING 2.** The checker IS the decision procedure. `DecidablePred WF`
is derived, computably, from `T010 + T011`. -/
def decidableWF_of_adequacy
    (hs : Sound check WF) (hc : Complete check WF) : DecidablePred WF :=
  fun r =>
    match h : check r with
    | .ok c => isTrue (hs r c h)
    | .error d => isFalse (by
        intro hwf
        obtain ⟨c, hcc⟩ := hc r hwf
        rw [h] at hcc
        exact nomatch hcc)

end Derived

/-! ## §3 — neither direction is redundant

Two independence witnesses over `Unit`, with `WF := fun _ => True` and
`WF := fun _ => False` respectively. They show that dropping either adequacy
direction breaks exactly one half of `T012`. -/

section Independence

/-- The always-rejecting checker. -/
def rejectAll : Unit → Except Unit Unit := fun _ => .error ()

/-- The always-accepting checker. -/
def acceptAll : Unit → Except Unit Unit := fun _ => .ok ()

/-- `rejectAll` is vacuously SOUND for any predicate: it never returns `ok`. -/
theorem rejectAll_sound (P : Unit → Prop) : Sound rejectAll P := by
  intro r c h; exact nomatch h

/-- **FINDING 3a.** Soundness alone does not give `T012`. `rejectAll` is sound
for `fun _ => True`, yet the FORWARD direction of `T012` fails: it returns an
error on a well-formed input. So the forward half genuinely consumes `T011`. -/
theorem forward_needs_completeness :
    Sound rejectAll (fun _ => True)
      ∧ (∃ d, rejectAll () = .error d)
      ∧ ¬ ¬ (True : Prop) :=
  ⟨rejectAll_sound _, ⟨(), rfl⟩, fun h => h trivial⟩

/-- `acceptAll` is COMPLETE for any predicate: it always returns `ok`. -/
theorem acceptAll_complete (P : Unit → Prop) : Complete acceptAll P :=
  fun _ _ => ⟨(), rfl⟩

/-- **FINDING 3b.** Completeness alone does not give `T012`. `acceptAll` is
complete for `fun _ => False`, yet the BACKWARD direction fails: nothing is
well formed and nothing is rejected. So the backward half genuinely consumes
`T010`. -/
theorem backward_needs_soundness :
    Complete acceptAll (fun _ => False)
      ∧ ¬ (False : Prop)
      ∧ ¬ (∃ d, acceptAll () = .error d) := by
  refine ⟨acceptAll_complete _, id, ?_⟩
  rintro ⟨d, hd⟩
  exact nomatch hd

end Independence

/-! ## §4 — per-clause reflection is NOT enough; clauses must be STAGED

`PROOF-DAG.md:518` prescribes "structural recursion plus decidable per-clause
reflection" for the Checker family. The estate's own experience contradicts the
flat reading. `Cas.Word.decidableReach` (`Cas/IR/Reach.lean:551`) has type

```text
decidableReach {w : Word} (hw : wf w = true) (a b : Addr32) : Decidable (Reach w a b)
```

— a decision that exists only RELATIVE to a prior structural gate `wf w`,
because the termination measure is the admission index (`wf_edge_index`,
`Cas/IR/Reach.lean:340`). Its docstring says so: "admission is what makes
reachability decidable here."

`ProgramWF` clause 5 (`HandlersWF`, `ALGEBRA.md:305`) quantifies over every
REACHABLE operation, and `EC1-K11` clause 3 (`CONTRACT-PACKET.md`) over every
REACHED service operation. If those readings are graph reachability, the same
premise-carrying shape applies and the flat conjunction of independently
decidable clauses is unavailable.

The positive result below is the shape that IS available. -/

section Staging

variable {α : Type} (P Q : α → Prop)

/-- **FINDING 4.** Staged decision: a clause decidable only under an earlier
clause still yields a decidable conjunction. This is the correct route for
`ProgramWF` when a later clause quantifies over reachability. -/
def decidable_staged [DecidablePred P]
    (dq : ∀ a, P a → Decidable (Q a)) (a : α) : Decidable (P a ∧ Q a) :=
  match (inferInstance : Decidable (P a)) with
  | isFalse hn => isFalse (fun hc => hn hc.1)
  | isTrue hp =>
      match dq a hp with
      | isFalse hq => isFalse (fun hc => hq hc.2)
      | isTrue hq => isTrue ⟨hp, hq⟩

/-- The staged decision is not a weakening: it still yields the full adequacy
the checker needs, i.e. it decides the conjunction and nothing less. -/
theorem decidable_staged_decides [DecidablePred P]
    (dq : ∀ a, P a → Decidable (Q a)) (a : α) :
    (P a ∧ Nonempty (Q a)) ∨ ¬ (P a ∧ Q a) := by
  by_cases hp : P a
  · cases dq a hp with
    | isTrue hq => exact Or.inl ⟨hp, ⟨hq⟩⟩
    | isFalse hq => exact Or.inr (fun hc => hq hc.2)
  · exact Or.inr (fun hc => hp hc.1)

/-- The estate's premise-carrying decision, cited as a live type, not retyped.
This `example` is the receipt that `decidableReach`'s signature is what §4
claims: a `Decidable` that CANNOT be an instance because its premise is a
hypothesis. -/
example : ∀ {w : Cas.Word}, Cas.Word.wf w = true →
    ∀ (a b : Cas.Addr32), Decidable (Cas.Word.Reach w a b) :=
  fun hw a b => Cas.Word.decidableReach hw a b

end Staging

/-! ## §5 — the decidability PROHIBITION is not enforceable by elaboration

`PROOF-DAG.md:221`: "`EC1-T011/T012` are prohibited if any `ProgramWF` clause
is silently changed to an undecidable semantic property."

That prohibition cannot be discharged by getting a file to elaborate.
Classically EVERY proposition is `Decidable`, so `DecidablePred ProgramWF` is
inhabited no matter how semantic the clauses become. The obstruction is
therefore invisible to the type checker and visible ONLY in the axiom receipt
and in whether `check` is a computable `def`. -/

section Enforcement

/-- **FINDING 5.** `Decidable` is classically inhabited for an arbitrary
proposition, so "this clause is decidable" is never a typechecking failure.
The receipt below is the whole point: this declaration reports
`Classical.choice`. -/
noncomputable def anyPropIsDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The same fact stated as a proposition, so the register can cite it: for
every predicate whatsoever there EXISTS a decision, classically. A checker
claim therefore has no content at the level of `Decidable` alone; it has
content only as a computable function plus its adequacy pair. -/
theorem decidability_is_never_an_obstruction {α : Type} (P : α → Prop) :
    Nonempty (DecidablePred P) :=
  ⟨fun a => Classical.propDecidable (P a)⟩

end Enforcement

/-! ## §6 — the `exists!` vacuity pattern, aimed at the AER clause

`ProgramWF` clause 11 (`AERWF`, `ALGEBRA.md:315`) is "synthesized `A/E/R`
normalizes to the declared triple". Its decidability depends on `SynthAER`
being a computable function. `SynthAER` appears in the packet ONLY in the
`EC1-T016` and `EC1-T017` rows (`PROOF-DAG.md:218-219`); it has no `EC1-D0xx`
defining term. So this section states the vacuity CONDITIONALLY, as the test
to run once the term exists — it does not assert that `T016` is vacuous.

The pattern is the one that already deleted rows in this packet
(`2026-08-31-effect-core-local-anchors.md` §3, four rows). -/

section Vacuity

/-- **FINDING 6-CARRIER.** `ExistsUnique` and its `∃!` notation DO NOT EXIST in
this environment. `formal/effect-core-v1/lakefile.toml` requires only `cas`,
`library/cas/lake-manifest.json` has an empty package list, and both toolchains
are `leanprover/lean4:v4.33.1` — no Mathlib anywhere. Every `exists!` row in
`PROOF-DAG.md` (`T004`, `T008`, `T016`, `T035`, …) must therefore be spelled
out or the notion defined locally, as here. -/
def ExistsUniqueL {α : Type} (P : α → Prop) : Prop :=
  ∃ a, P a ∧ ∀ b, P b → b = a

variable {Rw A : Type}

/-- **FINDING 6a.** If a relation is a function graph, `exists!` holds with no
premise at all. -/
theorem exU_graph_unconditional (f : Rw → A) (r : Rw) :
    ExistsUniqueL (fun a => a = f r) :=
  ⟨f r, rfl, fun _ h => h⟩

/-- **FINDING 6b.** The sharper form: the well-formedness premise is INERT.
This proof never touches its premise. If `SynthAER` turns out to be
`fun r a => a = synth r`, then `EC1-T016` is this theorem and proves nothing
about `ProgramWF`. -/
theorem exU_graph_premise_inert (f : Rw → A) (WF : Rw → Prop)
    (r : Rw) (_hwf : WF r) : ExistsUniqueL (fun a => a = f r) :=
  exU_graph_unconditional f r

/-- The contrast: `exists!` over a genuine RELATION is real content. Here is a
relation for which uniqueness FAILS, so the shape is not automatically empty —
which is why `SynthAER`'s definition, not its row, decides the question. -/
theorem exU_can_fail :
    ¬ ExistsUniqueL (fun _ : Bool => True) := by
  rintro ⟨b, -, huniq⟩
  have h1 : true = b := huniq true trivial
  have h2 : false = b := huniq false trivial
  exact Bool.noConfusion (h1.trans h2.symm)

end Vacuity

/-! ## §7 — the anchor carries `T012`'s exact shape

`2026-08-31-effect-core-local-anchors.md` §4.2 classifies `T012` as INHERITS
from `checkRefs_ok_iff` (`Cas/Core/Admission.lean:60`). VERIFIED: the line
resolves, the theorem is the stated iff, and the row's form is derivable from
it in three lines — including the derived `Decidable`, which §2 predicted. -/

section Anchor

open Cas

/-- **FINDING 7a.** `EC1-T012`'s shape at the shipped anchor, from
`checkRefs_ok_iff` alone. `checkRefs` returns `Except AdmissionError Unit`, so
`RefsOk` plays `ProgramWF` and `AdmissionError` plays `Diagnostic`. -/
theorem checkRefs_error_iff {σ : Store} {rs : List Ref} :
    (∃ e, checkRefs σ rs = .error e) ↔ ¬ RefsOk σ rs := by
  constructor
  · rintro ⟨e, he⟩ hok
    rw [checkRefs_ok_iff.mpr hok] at he
    exact nomatch he
  · intro hn
    cases h : checkRefs σ rs with
    | ok u =>
      cases u
      exact absurd (checkRefs_ok_iff.mp h) hn
    | error e => exact ⟨e, rfl⟩

set_option warn.classDefReducibility false in
/-- **FINDING 7b.** And the decision procedure falls out, computably, exactly
as §2 says it must. `RefsOk` is a `∀ ∈ list, ∃` statement whose decidability is
NOT obvious from its syntax — it is the checker that supplies it. -/
def decidableRefsOk (σ : Store) (rs : List Ref) : Decidable (RefsOk σ rs) :=
  match h : checkRefs σ rs with
  | .ok u => by cases u; exact isTrue (checkRefs_ok_iff.mp h)
  | .error _ => isFalse (fun hok => by
      rw [checkRefs_ok_iff.mpr hok] at h; exact nomatch h)

/-- The anchor's soundness half is separately shipped and is STRICTLY MORE
than `T010` asks: it names the violated clause. Cited to record that the
estate's admission pair is `ok_iff` + `error_condemns`, and that `T012` uses
only the first. -/
example {σ : Store} {rs : List Ref} {e : AdmissionError}
    (h : checkRefs σ rs = .error e) : e.Condemns σ rs :=
  checkRefs_error_condemns h

/-- `EC1-CE031` / `R16` compatibility receipt: the estate's completeness is
EXISTENTIAL in the error, and `T012`'s forward direction asks for exactly that
existential — so `T012`, unlike the deleted `T015`, is already R16-shaped. -/
example {σ : Store} {rs : List Ref}
    (h : ∃ e, AdmissionError.Condemns σ e rs) :
    ∃ e', checkRefs σ rs = .error e' :=
  checkRefs_complete h

end Anchor

/-! ## §8 — the twelve-clause decidability census (prose; no new theorems)

`ProgramWF` (`EC1-A12`, `ALGEBRA.md:295-317`) is a conjunction of twelve named
clauses. `PROOF-DAG.md:221` prohibits `T011`/`T012` if any clause is silently
semantic. This is the census the prohibition needs, with every estate anchor
line VERIFIED by reading the file.

| # | Clause | Decision procedure visible? | Anchor / risk |
|---|---|---|---|
| 1 | `IdsWF` — tables duplicate-free, references resolve | YES, unconditionally | `Cas/IR/Word.lean:150` `wf` is exactly this ("closure, kind discipline, and acyclicity in one executable predicate"); `Cas/Core/Admission.lean:49` `checkRefs` + `:60` `checkRefs_ok_iff` is the resolve half with its adequacy iff. |
| 2 | `TypesWF` — parameters/arg maps/ops/exits/interfaces "agree exactly" | YES, if `ValueTy` gets `DecidableEq` | "agree exactly" is syntactic equality over finite tables. Estate pattern: `Cas/Core/Node.lean:50` `instance (n : Node) : Decidable n.WF`. |
| 3 | `RowsWF` — rows canonical; escaped typed failure in `E` | FIRST HALF YES; second half RISK | Canonicality: `Cas/Core/Canonicalize.lean:77` `Decidable (c.IsCanon a)`. "Escaped" is a dataflow/reachability property, not a per-row check — see #5. `EC1-CE030` forces `NodupKeys` before any row-normalization transfer. |
| 4 | `RegionsWF` — region nesting acyclic, tokens do not escape, exits routed | ACYCLICITY YES; ESCAPE NO ANCHOR | Acyclicity: `Cas/IR/Reach.lean:416` `reach_acyclic`, `Cas/Schema/Guarded.lean:421` `instance (d : Document) : Decidable d.Guarded` (cycle-freedom of a non-suspend edge relation, decided by a walk). Escape: the corpus contains ZERO `Region`, `lifetime`, `supervisor`, `finalizer` declarations (censused). New construction. |
| 5 | `HandlersWF` — one typed clause per REACHABLE operation | CONDITIONALLY, and this is the pivot | `Cas/IR/Reach.lean:551` `decidableReach` decides reachability ONLY under `wf w = true`, and deliberately carries no `instance`. If "reachable" is graph reachability, clause 5 is decidable but PREMISE-CARRYING on clause 1 (§4). If "reachable" means "some execution reaches it", the clause is semantic and `PROOF-DAG.md:221` fires. **This reading must be pinned before `T011` is dispatched.** |
| 6 | `ResumeWF` — one SYNTACTIC owner, no duplicate consumption WITHIN A SINGLE TRANSITION | YES | Both bounds are already written into the clause. This is the clause the packet fenced correctly. |
| 7 | `FibersWF` — handles carry indices; scoped handles cannot outlive supervisor | INDICES YES; OUTLIVE NO ANCHOR | Index presence is a typing check. "Cannot outlive" is decidable only as a syntactic nesting discipline. Same vocabulary gap as #4. |
| 8 | `ResourcesWF` — resource tokens cannot escape scope; release body types | TYPES YES; ESCAPE NO ANCHOR | Same as #4/#7. |
| 9 | `ForeignWF` — every foreign ID resolves in the registry | YES | `Cas/Schema/Declarations.lean:202` `DeclarationId.all_complete`, `:276` `General.all_complete`, `:288/:297` `row_surjective`/`row_inj` — a closed registry with total unique lookup, already shipped. |
| 10 | `EntryWF` — entry accepts its declared input; every normal return has type `A` | YES | "Every normal return" enumerates the graph's `ret` terminators. Finite, syntactic. |
| 11 | `AERWF` — synthesized `A/E/R` normalizes to the declared triple | **BLOCKED** | `SynthAER` has NO defining term in the packet: it occurs only in the `EC1-T016`/`EC1-T017` rows (`PROOF-DAG.md:218-219`), with no `EC1-D0xx`. Worse, `EC1-CE008` (`div4_envelope_does_not_bound_the_error_row`, `2026-08-31-effect-core-classification-anchors.lean:143`) proves the estate's static summary does NOT bound the error row, and `EC1-T017` is NO ANCHOR. An EXACT static `E` is refuted at the CAS sublanguage; a MAY over-approximation is decidable but then "normalizes to the declared triple" must be restated as containment. |
| 12 | `PresentationWF` — normalization does not change reference MEANING | RISK, reading-dependent | Syntactic reading (resolved targets agree before/after) is decidable; model: `Cas/Schema/Basis.lean:634` `toRepresentationJson_eq_iff_repNorm`. Denotational reading of "meaning" is semantic and fires `PROOF-DAG.md:221`. R4 (identity hashes presentations, not denotations) argues for the syntactic reading, but the clause does not say so. |

**Verdict of the census.** Five clauses (1, 2, 6, 9, 10) have an unconditional
decision procedure with a shipped estate anchor. Two (3-first-half, 12) are
decidable under a syntactic reading that the clause text does not pin. One (5)
is the pivot: decidable but PREMISE-CARRYING, and only under the graph reading.
Three (4, 7, 8) have no estate anchor for their escape/lifetime halves. One
(11) is BLOCKED on a term that does not exist and carries a live
`VERIFIED-KERNEL` counterexample against its exact reading.

So `T012` is not at risk from its own statement (§1-§3). It is at risk only
through `T011`, and `T011` is at risk through clauses 5 and 11.

-/

/-! ## Receipts -/

section Receipts

#print axioms check_error_iff_of_sound_complete
#print axioms error_imp_not_wf
#print axioms not_wf_imp_error
#print axioms decidableWF_of_adequacy
#print axioms rejectAll_sound
#print axioms forward_needs_completeness
#print axioms acceptAll_complete
#print axioms backward_needs_soundness
#print axioms decidable_staged
#print axioms decidable_staged_decides
#print axioms anyPropIsDecidable
#print axioms decidability_is_never_an_obstruction
#print axioms exU_graph_unconditional
#print axioms exU_graph_premise_inert
#print axioms exU_can_fail
#print axioms checkRefs_error_iff
#print axioms decidableRefsOk

end Receipts

end EffectCoreScoutT012
