# Shared captured sources receipt

Ref callbacks and SynchronizedRef wrappers now use one relocation implementation and typing law.
The public module operations and their stored programs stay unchanged.

Base: `804fdc5e` with the coordinator's module integration pending.
The earlier SynchronizedRef receipt records the original module-local names.
The plan is `docs/research/2026-10-09-shared-capture-plan.md`.

## Change and proof placement

`Step.relocate` and `Step.freeze` live in `src/Effect4/Step/Callback.lean`.
The first iterates existing `Term.weaken` for appended caller slots.
The second retains the original source environment and refusal path.
The callback uses one relocation.
The wrapper supplies its reached environment.

`Step.relocate_types`, `Step.reached_slots`, and `Step.freeze_kept` move into `src/Effect4/Laws/Step/Callback.lean`.
Their statements and proofs retain the same premises.
`Step.callback_capture_types` now consumes `Step.relocate_types`.
`SynchronizedRef.modify_answers` consumes `Step.freeze_kept` for self and captured inputs.
The former module-local definitions and proofs are removed.
The existing callback reading law retains its statement and single-binder scope.

Concept: `store-typing`; requirement R4.
Role: compatibility helpers for `step-language-typed`, `fold-typed-atomic-update`, and `waiting-wrapper-typed` consumers.
The plan places the helpers before the move.
Typing requires aligned caller lengths, original source typing, and the existing reached-scope premise.
The move establishes no new allocation, membership, lock ownership, scheduling, or host claim.

## Checks

| Command or comparison | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Step.Callback Test.Program.RefFaces Test.Program.StreamArray Test.Program.SynchronizedRef` | Pass, 968 jobs |
| `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-09-module-array-sync-review.lean` | Pass; nested folds and caller-depth controls |
| Public packet production after the move | Twelve callers pass program admission with explicit read-back results |
| Twelve emitted files and the manifest against the pre-move packet | Byte-identical |
| Existing SynchronizedRef battery | Pass; collisions, nested capture, handles, malformed inputs, and original refusal path |
| Independent source review | Definitions and moved proof bodies retain their original form, except namespace references |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws Tools.LoadPaths Drivers.Semantics` | Pass, 830 jobs |
| Combined scoped audit | Pass; 920 compiled declarations across 21 selected modules |

The combined audit includes the unchanged native-term baseline while the target helper investigation remains open.
It allows only `propext` and `Quot.sound` among the checked dependencies.
Core imports exclude Laws.
The independent model modules exclude program implementation machinery.
The log is `docs/research/2026-10-09-shared-capture-audit.log`.

The source comparisons use `/tmp/effect4-module-catalogue-target-v2` and `/tmp/effect4-module-catalogue-capture`.
The finite program controls retain scope-sensitive sources and sources with their own fold binders.
They do not replace the conditional typing statements.

## Measured reuse

The combined imported environment contains 13,493 authored theorems and 260 semantics registry roots.
Its report records the following local measurements.

| Selected law modules | Theorems | Tree edges | Local edges | Reuse ratio | Reachable from registry roots |
| --- | --- | --- | --- | --- | --- |
| Stream.Array | 3 | 2 | 1 | 66% | 2 |
| SynchronizedRef | 7 | 25 | 7 | 78% | 0 |
| PubSub | 23 | 41 | 17 | 70% | 17 |
| Step.Callback | 9 | 10 | 7 | 58% | 3 |

Moving a lemma changes these edge categories without changing its mathematical content.
The percentages measure dependency edges, not proof quality, execution coverage, or work saved.
The Step callback module has no unconsumed theorem in this environment.
Its typing helpers have consumers but no current registry-root path.
SynchronizedRef's three public typing readers also lack a current root path.
Its composed-run statement remains open.
No theorem is removed because of those measurements.

The new module target packet still reports the known public tuple-annotation failure.
This source consolidation changes none of that packet's emitted bytes.
No sweep, primary-checkout edit, merge, or push occurs in this slice.
