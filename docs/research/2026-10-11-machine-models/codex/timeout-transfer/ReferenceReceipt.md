# Shared command reference transfer

The transfer proves local reference preservation. It does not produce Timeout's active generation or its cleanup order.

## Placement

Concept: store-typing, R4, and scope-lifetime-finalization, R11.
Question: `HeapSites.heap_sites_keep`, `Timeout.cleanup_keeps`, and `Timeout.retries_declared`.
Consumer: `SourceScope.command_heap` and `HostTimeoutNumberState.reference_command_heap`.
Reach: every native command, table, stored machine, command suffix, and drive budget.
The numeric consumer requires the actual captured source point at the current heap.
The result establishes no reached numeric history, progress, or host agreement.

## Sources

The host checkpoint is `125865d206dfedd3434d460010366f4fd136d84b`.
The dependency baseline includes R2 and the coordinator's checked reference reader slice.
The exact baseline and result hashes are in `/private/tmp/command-ref-transfer-hashes.tsv`.
The two-path patch is `/private/tmp/command-ref-transfer-proofs.patch`.
Its SHA256 is `61922762b969ec41644e83bfccdec87b97c8f234ff68b37cf63a9a2b84182e71`.

## Change

`NativeHeapExecution` moves its sole generated command analysis into `StoreExecution.command_refTransfer`.
`CommandRefTransfer` retains the actual owner lookup, command, synchronous head, unparked condition, and store answer.
The native wrappers cover scope exit, runloop interruption, and forced yield.
The five existing heap theorem headers remain byte-identical.
Their bodies become reference-predicate instances of the shared transfer.
The old `iteration_heap` configuration premise remains for compatibility; its transfer no longer requires that premise.
The coordinator's `native_row`, `refPeek_other`, and `primitive_refPeek_other` reader declarations remain unchanged.
The numeric consumer restricts permission to the actual loop or delivery owner.
It accepts unchanged references or an exact captured point with the numeric source permission.

Unchanged references do not identify an unexecuted operation.
The primitive producer retains the synchronous branch even for a read or an extensionally unchanged write.
Phase accounting must consume the exact operation and answer evidence; the locality relation alone cannot issue that evidence.

Measured file lengths:

| File | Before | After |
| --- | ---: | ---: |
| `NativeHeapExecution.lean` | 216 | 338 |
| `HostTimeoutNumberState.lean` | 380 | 404 |

The old private command body is removed in the same slice.
The shared producer contains the one command analysis; this adds no second native or third scenario command analysis.

## Verification

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.NativeHeapHistory Test.Dogfood.Proofs.HostTimeoutNumberFormFamily Test.Dogfood.Scenario.Timeout`
passes, 1182 jobs.
Log: `/private/tmp/command-ref-transfer-consumer-build-3.log`.

`LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/command-ref-transfer-audit.lean`
passes.
The audit covers both changed modules: 141 declarations within `[propext, Quot.sound]`, zero planned goals, zero modulo planned goals.
Log: `/private/tmp/command-ref-transfer-audit.log`.

`git diff --check` passes for both changed paths.
The five preserved theorem headers pass a byte comparison against the dependency baseline.
No executable source changes in this slice; no additional behavior gate is owed.

## Remaining work

The original stale-reply endpoint already passes its build and audit.
The original retry and cleanup endpoints remain planned goals.
Their producer must connect the root retry cursor, exact captured cells, active attempt, actual loser join, and completed timeout outcome.
A raw repeated count write remains outside that producer; this slice admits no weakened reached-history premise.
The next existing producer to refine is `SourceScope.source_action_at`, retaining exact child points before generation ownership is assigned.
