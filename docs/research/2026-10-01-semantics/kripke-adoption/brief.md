# Kripke and TAPL: adoption into Gemini's proof sequence

The owner ratified decisions **176(b)** (built layers use `Val.context` / `ctxImage`) and
**184(a)** (the exact-name initialized attribute handle with stale checks), then requested this
theory-aligned obligation pass. These rulings do not certify the unfinished layer repair.

This is a documentation and research handoff, **not a landing of production proofs**. Preserve
Gemini's active work. Continue its M5 → M6 → M7 sequence; insert the tasks below at their named
consumers. No duplicate ledger, general modal framework, new representation or full proof sweep.

## Baseline and evidence

Source review: main `01e3118065e64ddc5f9d28f0a0d982b5f8c647cd`. Gemini has separately committed
`a8cc8866`, the `evalTerm_fits` adapter; do not redo it. The two copied probes were compiled at
**845ce06e09dffd6b9f19cbe46f795566a602d5e3**, before the consolidated definitions. They are
historical evidence requiring verification against the adoption revision, not current report witnesses.

- `ResumeProbe.lean`: 8 printed declarations; Lean 4.33.1, exit 0, 2.728 s.
- `WriteProbe.lean`: 13 printed declarations; Lean 4.33.1, exit 0, 2.859 s.
- Saved passing receipts and logs accompany the exact, hash-checked probe bytes. All printed axiom
  footprints are within `[propext, Quot.sound]`. Commands use one process, `-j1 -M4096`, warnings
  as errors; the original runner imposed a 180-second bound.
- Original setup/import verification, source comparison and failed attempts remain at
  `/private/tmp/codex-second-eyes-2026-10-01/kripke-followup/`. These copied receipts retain their
  historical absolute paths; prepare imports for the new revision instead of executing them blindly.
- Earlier modal, quantifier-order and impossible-post controls are retained in
  `docs/research/2026-10-01-kripke-research/KripkeProbe.lean` with that pass's receipt.

## The theoretical contract

TAPL's author-hosted [contents](https://www.cis.upenn.edu/~bcpierce/tapl/contents.pdf) verifies
§8.3 (progress/preservation), §§13.4–13.5 (store typings/safety), and §§15–16 (subtyping and its
metatheory). It does not verify the bodies of those results. The vendored primary PLF
`sources/plf/References.v` supplies directly inspected statements: `store_weakening` at 1539,
`store_well_typed_app` at 1556, `preservation` at 1604 and `progress` at 1719; its
[published chapter](https://softwarefoundations.cis.upenn.edu/plf-current/References.html) agrees
in requiring a typed store and allowing a larger store typing after a transition.

Effect4 adapts that method, not that entire calculus. Stored programs are first-order trees;
semantic continuations are Lean functions. The bridge is source admission → `DenotesTyped` →
`TypedProg` → handler fulfillment → `ConfigTyped` preservation → the scoped M7 observation.
Do not infer a link from a similar theorem name: each arrow needs its actual premises.

For Kripke terminology, Ahmed's thesis §2.2.5, pp. 33–35 defines unary world-indexed predicates
with persistence; the vendored text and the earlier literature review give the locator. Here
`leHost` means compatible extension, not operational time or reachability. `Fits` and closed
continuations persist; complete state validity need not. Reference membership consults syntactic
declarations rather than recursively interpreting heap contents. This is why the present finite
definition needs no step index. No binary equivalence or execution weakest-precondition theorem
is supplied by that fact. Keep Hazel's reply-postcondition order distinct from world extension.

## K0 — make the interpretation match the evidence

Do this with the next report-maintenance slice, without delaying current M5 arms.

1. Keep the corrected `semantics.md` responsibilities table and system-map wording. For each
   touched concept, record a short chain: **source definition/technique → local judgment and
   cut → exact proposition and premises → consuming proof → accepting/rejecting control**.
   Existing witnesses are linked, not redeclared. A selected-claim list is not a coverage proof.
2. Fix the concrete registry/prose mismatches at the source of the report:
   - `store-safety` currently has role `.progress` and cites TAPL safety as `excludedFeature`.
     Retain its identity for *store-content preservation*: use `.preservation`, state its
     planned composition from `storeStep_typed` into M6, and keep it absent until the selected
     statement exists. The existing `scheduler-progress` claim already owns transition/frontier
     existence; do not count it twice. Store safety is an adaptation, not an excluded feature.
   - `m7-never-halts` keeps its goal pointer and fragment, but has role `.adequacy`, matching
     the neighboring M7 consequences. Its conclusion is not successor existence.
   - Prose summaries of `DenotesTyped` must keep source formation, service-table equality,
     source-node lookup and point admission visible; use the generated exact proposition.
3. For formation, canonical forms/inversion, binder/environment transport, normalized subtyping,
   initialization and preservation, link an existing theorem or a named open consumer. An
   inapplicable lambda beta-substitution theorem is a documented cut, not missing implementation.
   Positional binders and capture environments still require their own extension/lookup laws.

No new API or role vocabulary is needed. Regenerate and run the existing semantics checker in
the proof worktree after changing the registry. A metadata correction must not move a proof status.

## K1 — preserve a queued resume at the lookup it actually reads

**Question:** which declarations must remain stable when allocation introduces a new token?
`Contracts.ResumeOk` (`Typed/Contracts.lean:91`) is conditional on `Θ target token`; at an absent
token it is vacuous. `Commands/Bookkeeping.lean:1121` already proves `resumeOk_world` under
equality of the whole token table. The historical probe proves the smaller interface:

```lean
w.leHost w' → w'.Θ target token = w.Θ target token →
  Contracts.ResumeOk (TypedProg root) w target token code →
  Contracts.ResumeOk (TypedProg root) w' target token code
```

Adopt that helper only with a real consumer in M6's open `step_loop` or `step_deliver`
parking/registration arms. The companion probe uses `w.Θ owner supply = none` and
`token < supply` to preserve the old resume under `w.addToken owner supply ty`, even when
`owner = target`. Keep the distinction between freshness of the new key and inequality of the
old key. Prove the bound from `QueueOk`/scheduler clauses; do not assume it at the final command
goal. Existing closed `step_resume` and stack monotonicity proofs need no duplicate obligation.

**Controls:** undeclared old token followed by a declaration incompatible with unit code must
refute unrestricted transport; correctly typed nat code must pass; same-owner insertion above
the old token must preserve it. On the adoption revision, verify imports match sources, compile
these controls, print axioms, and use the helper in the consuming proof. Keep whole-table equality
where the rest of a caller reads the whole table; a local helper does not justify a global weakening.

## K2 — connect existing store adequacy to actual command preservation

`Typed/Adequacy.lean:51` (`StoreImplements`) and `:60` (`storeStep_typed`) already require an
actual result, `leHost`, a typed resulting store and a typed continuation. `refSet_implements`
at 664 and `refMake_implements` at 604 are existing instances. M5 group 4 establishes protocol typing and later-world continuation
typing; M6's store arms use these operational adequacy lemmas to meet those protocols. Connect
these two responsibilities without requiring handler execution proofs in M5. Do not reopen the
existing instances merely to put “Kripke” in their names.

**Control worth retaining:** the historical write probe has two well-formed stores and an actual
write respecting `leHost`, yet strong `StoreTyped` fails when a reference is written with the wrong
declared referent type. Actual `storePre` rejects it; the correctly typed write succeeds. This
demonstrates why new-value membership is necessary, not a reached runtime failure.

At each consuming arm name: old-store typing, request permission, new-value membership, freshness
where allocating, declaration preservation, and the remaining stack/queue/validity clauses. A
postcondition used to type continuations must be met by the actual handler; quantifying over an
impossible post is not enough. Keep shared intermediate witnesses outside future-world quantifiers
where both code and stack need the same type (`∀ w, ∃ t` does not supply `∃ t, ∀ w`).

For scope/memo validity at `unknown`, link the existing row 180/M7 obligation and Assembly's stated
gap. The follow-up allocation candidate was never compiled. Do not mint a new finding or call the
older scope-post repair incomplete on its account.

## Correct D5's transport premise, then continue its existing goals

D5 step 1 says each new clause must be monotone. Read that with this correction: classify each
field as (a) persistent with its named theorem, (b) dependent on stable lookups/freshness, or
(c) re-established by the actual transition. Keep initial establishment and every writer in the
existing row 181 field census. Never demand unconditional monotonicity from conditional resume
typing or exact support/coverage. `StepPreserves` (`Assembly.lean:445`) owns the whole transition.

## The next safety question after the current preservation slices

The existing `scheduler-progress` claim remains open. After the relevant M5/M6 fragment is
assembled, select a bounded configuration/decision fragment and state its finished, genuinely
stepping, or live-frontier alternatives. A no-op transition must not make the progress claim
vacuous. Explicitly distinguish an unavailable host reply or decision from a shape failure and
keep infinite fairness separate. This is a later task under the existing claim, not a new
prerequisite that interrupts current proof work.

The term boundary already has evaluation-existence evidence: `evalTerm_progress`
(`Typed/Denotation.lean:517`) assumes the native atom table and `FitsAll`, and returns a value
with membership; `evalTerm_progress_env` (`:573`) adapts it to `EnvTyped` and a source signature.
The earlier tentative missing-property question is withdrawn. Reuse those theorems alongside
`TermFits`, whose separate statement assumes successful evaluation. The
[book-guided proof cards](../types-2003-scout/proof-cards.md) also identify the existing helper
for the load connector's marker premise, with its import-placement constraint. Neither is a new
semantic obligation; do not strengthen the completed adapter or duplicate the existing results.

## Pierce-informed critique: our inference, not attributed advice

- **A theory name outruns its theorem:** “weakest precondition,” “progress,” and “Kripke” need
  separate local definitions and connector theorems. Fix the names before adding proof machinery.
- **A monolithic world conceals different premises:** preserve declarations, type new contents,
  and establish state validity separately. Use existing small interfaces; a new world hierarchy
  is justified only if a concrete consumer needs it.
- **One type has competing value encodings:** row 176(b) removes this ambiguity. Keep the image,
  its reader and the typing rule coherent, with memo-hit and fresh-build controls.
- **Chapter placement masquerades as coverage:** use a finite responsibility map for the actual
  language fragment. Missing progress and existing preservation evidence must stay distinguishable.

## Completion for each future slice

One exact claim, one existing ledger owner or selected-report pointer, one consuming proof, named
premises and fragment, and retained positive/negative controls. Narrow tests and axiom receipts
precede status updates. No runtime-safety, liveness or target-equivalence claim follows just from
these research probes. The owner requested this consolidation while production fronts merge;
this packet itself implements no Lean source or generated-report change.
