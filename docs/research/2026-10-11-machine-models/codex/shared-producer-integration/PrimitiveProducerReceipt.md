# Shared primitive producer receipt

The slice removes two duplicate primitive evaluator classifications.
It retains every replaced theorem header and the actual synchronous operation, value, and returned frame.
It closes no original Timeout numeric goal.
The final step witness also retains every actual generated dispatch exclusion.

## Snapshot

Checked worktree head: `125865d206dfedd3434d460010366f4fd136d84b`.
Coordinator head at verification: `9643905ab44ce058318c937fa16b4ac9d33ede67`.
The three replaced files match that coordinator's current baseline bytes.
The worktree contains copied coordinator dependencies; those copies remain excluded from the patch.
No runtime file changes in this slice.

Patch: `/private/tmp/primitive-producer-proofs.patch`.
SHA256: `ab222aad8bad5b0f5ff7b7902c55f23ef8b66b115b7be89c9de1c51b1d39b148`.
Baseline and final hashes: `/private/tmp/primitive-producer-snapshots.tsv`.
Dependency hashes: `/private/tmp/primitive-producer-hashes.tsv`.
The snapshot files use `/private/tmp/PrimitiveChecked<basename>`.

## Placement

Concepts: reactive-scheduling R11 and store-typing R4.
Questions: `evaluation-moves`, `HeapSites.heap_sites_keep`, `Timeout.cleanup_keeps`, and `Timeout.retries_declared`.
The shared producer serves lexical configuration, reference transfer, and executed store certificates.
It connects actual M5 evaluation to M6 ownership and operation evidence.
It supplies no host agreement, progress, or numeric history guarantee.

`Moves.PrimitiveProducer` in `src/Effect4/Laws/Program/PrimitiveProducer.lean` retains existing evaluator-family results.
`Moves.evaluatePrim_producer` uses the generated primitive eliminator once.
Each successful sync retains its thunk, unparked selection, actual state equation, value, and exact returned iteration.
Registration and fiber actions retain their actual interpreter hooks.
The generic relation makes no unconditional reference-equality claim for those hooks.

`Moves.PrimitiveProducer.tracedFootprint` in `src/Effect4/Laws/Program/Footprint.lean` supplies the existing frame and event observation.
`SourceScope.primitive_at` in `src/Effect4/Laws/Program/NativeExecutor.lean` consumes the same producer under its existing source premises.
`StoreExecution.primitive_refTransfer` in `src/Effect4/Laws/Program/NativeHeapExecution.lean` consumes it under the native interpreter.
The old generated evaluator passes in those consumers are deleted.

`PrimitiveProducerReader.read` and `write_same` in `Test/Dogfood/Proofs/PrimitiveProducerReader.lean` apply actual allocated-cell laws.
Both retain executed-operation evidence while the reference heap stays equal.
They establish one native evaluator call under explicit allocated-cell and current-code premises.
They establish no source permission or execution-history invariant.

## Verification

The current public headers before `:=` compare byte-for-byte with the retained baseline:

- `evaluatePrim_tracedFootprint`;
- `primitive_at`;
- `primitive_refTransfer`.

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.NativeExecutor Effect4.Laws.Program.NativeHeapExecution` passes all 525 jobs.
Output: `/private/tmp/primitive-producer-consumers-2.log`.
Its dependency check includes the shared producer, Footprint, NativeCommands, NativeHistory, and NativeReferences.

`LEAN_NUM_THREADS=3 lake env lean /private/tmp/PrimitiveProducerReader.lean` passes.
Output: `/private/tmp/primitive-producer-reader.log`.
`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.PrimitiveProducerReader` passes all 822 dependency jobs.
Only the reader module rebuilds in that run.
Output: `/private/tmp/primitive-producer-reader-build.log`.

`LEAN_NUM_THREADS=3 lake env lean /private/tmp/PrimitiveProducerAudit.lean` passes.
The audit includes all four proof modules and the reader.
Output: `/private/tmp/primitive-producer-audit.log`.
Result: 287 declarations within `[propext, Quot.sound]`, zero modulo declarations, zero planned goals.

The owned-file diff check passes.
No executable definition changes, so this proof-only slice owes no behavior run.
Wider consumers wait for the coordinator's build slot.

The strengthened producer and frame projection pass all 337 narrow jobs.
Output: `/private/tmp/primitive-producer-dispatch-build-3.log`.
Both actual lexical and reference consumer files pass direct Lean checks, sequentially.
Outputs: `/private/tmp/primitive-producer-NativeExecutor-dispatch-check.log` and `/private/tmp/primitive-producer-NativeHeapExecution-dispatch-check.log`.
The final snapshot audit uses these exact checked outputs through a private dependency overlay.
Output: `/private/tmp/primitive-producer-dispatch-audit.log`: 287 allowed declarations, zero goals or modulo declarations.
The earlier 525-job consumer build precedes this dispatch strengthening; the wider graph remains scheduled by the coordinator.

## Size

| File | Before | After |
| --- | ---: | ---: |
| PrimitiveProducer | 0 | 146 |
| Footprint | 446 | 457 |
| NativeExecutor | 141 | 160 |
| NativeHeapExecution | 338 | 334 |
| PrimitiveProducerReader | 0 | 47 |

The three existing primitive classifications become one shared classification.
The new evidence retains information that the old frame labels erase.
The slice adds 219 net lines including the reader.
It does not claim a net line reduction.

## Open connections

The conservative reference footprint includes reads and allocation's actual returned key.
It is not an exact write census.
The store-label consumer must interpret the same actual operation and answer through existing `Contracts.Path`.

The numeric instance still owes live generation permission and persistent cleanup provenance through actual history.
The loser join must produce completed-cleanup permission before the root's form finalizer uses it.
The original fixed scenario budgets remain explicit at the actual entry prefix.
No arbitrary-fuel count atomicity, raw-answer-label permission, or new history premise is introduced.

The coordinator adds the new reader to `Test/All.lean`.
No root import or gate file is edited in this worktree slice.
