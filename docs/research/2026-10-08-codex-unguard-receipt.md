# UNGUARD, P3 and P2b: Codex receipt

Main already contains P3 and UNGUARD at `75529f68`. Merge the remaining P2b rules, printer, proofs and controls together.
The raw reader still refuses inserted arguments before the named erasure.
The coordinator must update the guarded-rule claims to the new statements and retain the open checker-monotonicity obligation.

Status: all assigned acceptance commands pass. The implementation is committed. This receipt records its checked head.

## Base, scope and commits

Base: `c51f9e6b7c456d952d0fe408a274432f4c9aebd5`.
Verified implementation head: `e1aaf620b58d0b62bd8252e8ed7b3124d504cde0`.
Branch: `codex/unguard`.
The following receipt commit adds evidence only.
Worktree: `/Users/pooks/.codex/worktrees/unguard/lean4-effect4`.

The owner approves W1, W2, parameter order, P3 before UNGUARD, and P2b in this landing.
P2b includes options, lists and folds, fibers, exits, and the four cause queries.

| Commit | Result |
| --- | --- |
| `41198cade3d0d08c5ae844afedf586aad73389d6` | P3: named syntax erasure and transport of existing reading laws |
| `667b6df564aa33148b837630e9cf1e0017ff5fb6` | UNGUARD: row and binder matching through `Bounds.matchB` |
| `6c18faf4` | P2b classifier rules, full fallback laws and closed-input consumers |
| `e1aaf620b58d0b62bd8252e8ed7b3124d504cde0` | Full typed printer, target controls and generated truth results |

Codex performs no merge or push. Coordinator-owned files remain unchanged.
[Changed files](2026-10-08-codex-unguard-evidence/changed-files.json) records every source path and hash from base to implementation head.

## What changes

The row checker and binder matcher use the existing bounds matcher.
The old term guard and its laws are removed.
W1 accepts joined request types. W2 accepts joined answers from an atomic modifying function.
Formation, captured environments and store typing remain separate premises.

The approved eliminators read every retained normalized member.
The fiber, list, exit and cause rules keep every successful raw answer.
The option rule keeps its normalized form.
A retained unsupported member still refuses the whole target.

The typed printer writes the required call arguments from actual checked contexts.
Its named erasure retains operation-owned arguments and stored type annotations.
The existing reader follows that erasure.
The raw printer and the general application facade remain separate consumers.

`NoJoin` includes both row insertions and the added typed sites.
`printTyped_eq_print` retains its conditional equality statement.
`annotate_eq_table` and both annotation source files remain unchanged.

The host boundary states template-variable order, with `.var 0` first.
The compiler controls inspect actual emitted calls and selected declarations.

The optional-record target helper distributes its answer over receiver alternatives.
Its runtime body and cast remain unchanged.
A single record's union-valued field retains its prior answer.
An old-alias-only mutation reproduces exactly the joined optional-record mismatch.

## Proof placement

The implementation plan records each obligation before proof work.
The [printer placement manifest](2026-10-08-codex-unguard-evidence/proof/p3-scout/final-theorem-placement-manifest.json) records every named printer declaration and its consumer.
The [P3 placement](2026-10-08-codex-unguard-evidence/proof/p3-placement.json), [row statements](2026-10-08-codex-unguard-evidence/proof/unguard-statements.json), and [P2b placement](2026-10-08-codex-unguard-evidence/proof/p2b-core-placement.json) record the earlier slices.
The [final status output](2026-10-08-codex-unguard-evidence/final/proof-status-final.log) retains full public statements, universes and transitive axioms.
Those historical packets retain their original stage labels. [Final acceptance](2026-10-08-codex-unguard-evidence/acceptance.json) supersedes their pending acceptance labels.

| Property | Concept | Claim or consumer | Reach | Exclusions | Requirement |
| --- | --- | --- | --- | --- | --- |
| Erased typed output reconstructs the ordinary print | exact-codecs | Proposed typed-print erasure claim; existing reading laws | Lawful spelling, readable source and successful typed print | No TypeScript or runtime theorem | R8 |
| Reading after erasure reconstructs the program | exact-codecs | Existing `read_print` and `read_exact` | Existing reader profile and successful erased reading | Raw foreign spellings need not be identical | R8 |
| Row and binder checking through bounds | subtyping-algebra; store-typing at module consumers | template-match-complete and operation typing | Existing formation, term, capture and environment premises | No general checker-monotonicity result | R4 and R14 |
| Full union lifting with raw-answer compatibility | subtyping-algebra | union-rule-extend; option, fold, fiber, scope and cause consumers | The member classifier's upper, least and monotonicity premises | No new target support or liveness result | R14; closed-input consumers serve R4 |
| Annotation equals the address table | initial-algebras-folds | annotate-table | Existing unchanged theorem | No cost theorem | R14 |

## Checks

Lean: `leanprover/lean4:v4.33.1`.
Every Lean command runs sequentially through `scratch/lean-slot.sh`.
The wrapper sets `LEAN_NUM_THREADS=2`.

The final command manifest records every command, exit code, output and source identity.
The axiom output and whole Test gate remain separate evidence from the compiler and finite controls.

| Check | Current evidence |
| --- | --- |
| P3 narrow build | `lake build Effect4.Laws.Codegen.PrintTyped Test.Codegen.PrintTyped`: exit 0, 340 jobs |
| P3 axiom queries | 46 production roots; permitted ceiling only |
| UNGUARD narrow build | Selected bounds, typing, template, module and print consumers: exit 0, 839 jobs |
| UNGUARD axiom queries | 14 production roots; permitted ceiling only |
| P2b narrow build | Union rules, eliminators, closed inputs and initial typed-print consumers: exit 0, 707 jobs |
| P2b initial axiom queries | 30 production roots; permitted ceiling only |
| Full typed-site proof | Production law and battery builds pass; all 16 final queried roots are proved with no remaining goal |
| `lake build Test` | Pass: 1,371 jobs; 850 modules and 97,885 declarations audited |
| `check-cases` and `check-proof-style` | Pass; existing policies and baselines stay unchanged |
| `check-ts-reader` | Pass: 742 tests and 3,650 expectations |
| `check-truth` | Pass: 76 agreements and the existing signed U-01 divergence |
| `check-target` | Pass: 88 selected items, 28 tests and 600 assignability pairs; six named cuts remain |
| `check-corpus` | Pass: all 400 rows match; 25 registered disagreements remain |
| `check-tsdiag` | Pass: 408 programs and 11 controls; no admitted program is refused by tsgo |
| `check-ingest` | Pass: exact oracles, transformations, refusals, pinned runtime and independent wire decoding |

## Exact final commands

All commands use the isolated worktree above and the pinned compiler named above.
The [command manifest](2026-10-08-codex-unguard-evidence/acceptance.json) also records duration, source identity and retained output.

| Check | Command | Exit |
| --- | --- | --- |
| printer-final | `scratch/lean-slot.sh lake build Effect4.Laws.Codegen.PrintTyped Test.Codegen.PrintTyped` | 0 |
| test-final | `scratch/lean-slot.sh lake build Test` | 0 |
| proof-status-final | `scratch/lean-slot.sh lake env lean -DwarningAsError=true /private/tmp/codex-unguard/FinalProofStatus.lean` | 0 |
| check-cases | `scratch/lean-slot.sh make -j1 -o ts/eff/node_modules -o harness/truth/node_modules check-cases` | 0 |
| check-proof-style | `scratch/lean-slot.sh make -j1 -o ts/eff/node_modules -o harness/truth/node_modules check-proof-style` | 0 |
| check-ts-reader | `scratch/lean-slot.sh make -j1 -o ts/eff/node_modules -o harness/truth/node_modules check-ts-reader` | 0 |
| check-truth | `scratch/lean-slot.sh make -j1 -o ts/eff/node_modules -o harness/truth/node_modules check-truth` | 0 |
| check-target-final | `scratch/lean-slot.sh make -j1 -o ts/eff/node_modules -o harness/truth/node_modules check-target` | 0 |
| check-corpus | `scratch/lean-slot.sh make -j1 -o ts/eff/node_modules -o harness/truth/node_modules check-corpus` | 0 |
| check-tsdiag | `scratch/lean-slot.sh make -j1 -o ts/eff/node_modules -o harness/truth/node_modules check-tsdiag` | 0 |
| check-ingest | `scratch/lean-slot.sh make -j1 -o ts/eff/node_modules -o harness/truth/node_modules check-ingest` | 0 |

## Final sweep repairs

The first whole Test run refuses two old focus expectations and the proof-style scan.
The focus controls now accept the approved two-fiber union and refuse a retained non-fiber member.
The existing typed-state command reserves `columns` in the scanner environment.
Quoting that identifier retains the same Lean name, definition and theorem statements.
The proof-style baseline and scanner remain unchanged.
Two unused companion helpers are removed before final acceptance.
The failed run remains in the evidence packet.
The truth inventory control adds the four assigned fixture names before regeneration.
The first target gate refuses their selection order. The corrected selection follows the producer without changing the inventory test.
The initial W1 runtime run parks because raw registration checks the uninstantiated reply column.
The bounded W1 adapter derives its single runtime row from `callAt` at address `[1]`.
Typing and printing retain the original generic row. Both runtime entries use the derived instance.
The manifest records both tables. Missing or mismatched instances refuse before output.
Raw-template refusals, both admitted payloads, an unsupported Boolean and a wrong source shape remain controls.
This establishes no general runtime-table substitution law or new host-session theorem.

## Compiler and finite evidence

Compiler: `@typescript/native-preview` `7.0.0-dev.20260629.1` only.
Effect target: `4.0.0-rc.112`.
The API receives the actual `Program.printTyped` bytes.
Project caches remain within their own snapshot.
The controls use parsed spans and exact diagnostic locations.
Rendered type strings decide no verdict.

The focused P2b packet records 52 successful type observations and 15 missing-member refusals.
Three separately named nonconforming observations remain retained.
Six prior target refusals remain retained.
The original optional-record mismatch and its repaired result remain available.
This packet establishes finite compiler checks and finite helper execution only.

All four W1/W2 runtime fixtures agree on exits, schedules and synchronous exits.
All 73 earlier manifest programs and recorded observations remain unchanged.
The refreshed lane records 76 agreements and the existing signed U-01 divergence.
A separate comparison records 157 passing identity and frozen-table checks.
The whole Test gate retains 30 existing planned goals and 12 declarations that depend on them.
The 16 queried slice roots are proved and depend on no goal.
The unchanged implementation boundary retains its 17-module, 23-declaration axiom exemptions.

## Coordinator updates proposed

- Update template-match-complete to remove the retired term guard from its description.
- Keep the retired template-match-anchored claim retired; use the bounds claim and its existing pointers.
- Update typed-print-connector to state the `NoJoin` premise across rows and typed sites.
- Add the new erasure and reader transport claims under exact-codecs and R8.
- Point union-rule-extend at `Eliminator.extendAll_laws` and describe full normalized fallback.
- Keep the legacy guarded helper laws available for their historical consumers.
- Bound `optionTy_eq_normal` by its retained normalized-member-count premise.
- Remove only the resolved guard blockers from checker-monotone. Keep its other premises and open proof explicit.
- Keep annotate-table unchanged.
- Retain every unrelated R1–R14 open part.

The coordinator owns decisions, the semantics registry, its generated report, Lake configuration and STATE.
This slice edits none of those files.

## Open boundaries

General checker monotonicity is not proved here.
The existing target refusals and named negative compiler observations remain visible.
The application facade is not globally switched to typed printing.
No outside implementation, concurrency, progress or liveness theorem follows.
The compiler and runtime controls are finite observations.
The unchanged corpus index and existing disagreement records remain explicit.
No package installation, main-checkout edit, merge or push occurs.

## Axiom output

The [whole Test output](2026-10-08-codex-unguard-evidence/final/test-final.log) audits all 97,885 declarations.
Semantic and test declarations stay within `[propext, Quot.sound]`.
The existing exact implementation exemptions remain unchanged.
The [public statement query](2026-10-08-codex-unguard-evidence/final/proof-status-final.log) reports the same permitted ceiling for every selected root.
No new goal, axiom exemption or proof-style exception is added.

## Evidence identities

The [packet hashes](2026-10-08-codex-unguard-evidence/packet-hashes.json) cover all retained evidence files.
The receipt retains initial failures beside their successful repairs.
The [truth comparison](2026-10-08-codex-unguard-evidence/final/truth-comparison.json) preserves all earlier program observations.
The [generated header check](2026-10-08-codex-unguard-evidence/final/generated-header-check.json) limits changes in 73 earlier modules to the shared import.
The initial header verifier expected the insertion at the wrong import. Its corrected check passes all 73 files.

The retained raw compiler input `target/p2b/printed.ts` ends with the producer's blank line.
The diff whitespace check excludes only that byte-preserved evidence file; every other committed path passes.
