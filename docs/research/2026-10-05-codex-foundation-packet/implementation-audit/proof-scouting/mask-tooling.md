# Mask proof scouting

Recommendation: use the existing goal and report tools; correct the mask's requirement entries before declaring its goals.
Evidence status: source inspection at `4977c4f3`, plus inspection of an existing report artifact.
Scope: decisions 244–246 and F10 of `docs/research/2026-10-05-claude-lead/mask-second-note.md`.
No Lean command, build, generator, installation, or repository edit ran.

## Three proof prerequisites

| Order | Obligation and consumer | Existing declarations to reuse | Boundary |
| --- | --- | --- | --- |
| 1 | Choose the saved bit's canonical image; prove its membership, inversion, and transport to later worlds. The getter, typed stores, and captured environments consume these facts. Place at store-typing, R4. | `Fits`, `FlatFits`, `fits_hasTy`, `fits_live`, `fits_mono`, and `live_of_handles_nil` in `src/Effect4/Laws/Program/Typed/Membership.lean` | State the image first. Add its clauses to the existing membership proofs. A value with no handles can reuse the existing liveness helper. Service carriers remain refused. |
| 2 | Type the getter's answer and the restore body at child zero. Connect them to M5's actual source-point induction. Place at residual-program-typing, R4. | `interruptible_arm`, `uninterruptible_arm`, `pointTyped_child`, and `childDenotes_upto` in `src/Effect4/Laws/Program/Typed/Denotation.lean`; `denotesTyped` in `src/Effect4/Laws/Program/Typed/LayerArm.lean` | Both saved choices must resolve the same checked body and environment. Reuse the existing child-body certificate, rather than inventing a scoped binder theorem. Neither constructor binds. |
| 3 | State restoration at region entry and exit, including pending causes. The waiting wrapper consumes this behavior. Place at scope-lifetime-finalization, R11. | `maskFrame` and `clause_mask` in `src/Effect4/Laws/Program/Typed/Commands/Evaluate.lean`; restoration cases in `src/Effect4/Laws/Machine/ScopeRestoration.lean` | The existing clause proves typed-state retention, not the new form's behavior. The scope-restoration lemmas concern completed scope cleanup. Reuse their frame cases without asserting they already prove the getter. |

The third obligation needs separate clauses for success, failure, pending interruption, and nested regions.
A false saved choice leaves the executing fiber's current flag unchanged.
The getter's restoring frame may interrupt before the body begins.
Keep the no-prior-acquisition premise from row 246 visible in the composed client law.
These obligations establish no progress claim or native-callback equality.

The TypeScript printer needs no duplicate round-trip theorem.
Extend `table_apart` and `table_shape`, then retain the existing `read_print` and `read_exact` statements.
Their declarations live in `src/Effect4/Laws/Codegen/ReadPrint.lean` and `src/Effect4/Laws/Codegen/Read.lean`.
A separate printed-behavior claim names the target release, decision relation, observation, and entry checkpoints.
It belongs under translation-simulation, R10, and may also serve R11.
An R8 round-trip theorem does not discharge that claim.

## The concrete record gap

F10 says each of its five obligation groups is already an open requirement part.
The current `Tools.Semantics.registry` does not explicitly record all five (`tools/Tools/SemanticsRegistry.lean`).

- R4's `scoped-body-substitution-boundary` still describes the first new scoped constructor, although the ratified restore node does not bind.
- R11's `saved-mask-restoration` still uses the older saved-state wording and cites row 227 alone.
- R4 has no explicit mask-image part, and R8 has no explicit extended-table part.
- R10 has no explicit mask profile or entry-checkpoint part.

Revise those entries against rows 244–246, while retaining each unrelated open part.
This is a record correction, not evidence that an implemented theorem fails.
The lack of mask goals is expected before the image and node definitions exist.
Once they exist, replace the corresponding open part with its placed goal and semantics registry pointer.
Retain any remainder that no proposition states.

## Use the existing tools directly

`proof_goal` creates the one theorem whose statement records the obligation (`tools/ProofGraph/Goal.lean`).
Add a `semantics` attribute with the concept and primary requirement.
Add a claim whose role matches its purpose and whose pointer is `.witness` of that goal.
`claimStatus` already accepts this pointer and reports it as wanted (`tools/Tools/Semantics.lean`).
Proving the goal changes its body in place; no second theorem or closing command is needed.

For a decomposition, write an ordinary theorem that actually uses the goals.
Alternatively, use `proof_sketch` to extract residual statements (`tools/ProofGraph/Sketch.lean`).
Its parts inherit the placement; its parent is proved modulo those parts.
The sketch command refuses universe-polymorphic statements, so use ordinary goals when that restriction applies.
The existing fixtures demonstrate this path in `Test/Audit/ProofGraphPlan.lean` and `Test/Audit/SemanticsCensus.lean`.

After the authorized narrow build, use `#plan_status` on the new goal and its actual M5 or M6 consumer.
Inspect `restsOn` and `nearest`, not only the requirement's placed-node list.
`buildPlan` reads dependency edges from proof terms (`tools/ProofGraph/Plan.lean`).
`planJson` associates tagged nodes with requirements through metadata (`tools/Tools/Semantics.lean`).
A placement establishes the authored association; it does not establish that M5 or M6 uses the declaration.
For a claim serving two requirements, use one primary placement and the existing second requirement's `top` list.
No new multi-placement mechanism is necessary.

Keep conditional premises in the statement review.
A theorem can report proved while requiring a strong hypothesis; that status means it reaches no planned goal.
The report does not certify the English claim's match to its proposition or the sufficiency of its premises.
`Claim.title` and `Requirement.openParts` are authored text in `tools/Tools/SemanticsRegistry.lean`.
Do not remove an open part merely because a nearby theorem is proved.

## Bounded report inspection

I parsed `.lake/gen/semantics-report/semantics.json`, an existing artifact last modified at 11:12 local time.
Its R4, R8, R10, and R11 rows all report open, with no next goals in those four rows.
Their open-part counts are 7, 6, 10, and 6 respectively.
The artifact reports no unplaced goals.
Those empty goal lists do not mean the requirements are finished.
`planJson` keeps each requirement open while any `openParts` entry remains.
The parsed JSON contains no source revision, so this review does not treat it as a fresh measurement of HEAD.

The practical improvement is the small semantics registry correction and a receipt that checks both placement and actual consumer dependencies.
No further tool mechanism is required for these mask obligations.
The next implementation receipt can reuse `make gen-semantics` and the existing report controls after the authorized build.
Neither command ran during this scout.
