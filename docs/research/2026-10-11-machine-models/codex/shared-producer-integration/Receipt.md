# Shared machine and producer integration

The whole law graph builds with the canonical machine writes and shared primitive producer.
The landing repairs Timeout's seven private evaluator reductions.
It closes no original planned goal.

## Placement

Concepts: reactive-scheduling R11, store-typing R4, and host-session-protocol R6.
The machine edit laws serve shared invariant transport.
The primitive producer serves `evaluation-moves`, `HeapSites.heap_sites_keep`, and the original Timeout numeric goals.
The exact source children serve lexical provenance and future generation permissions.
These facts supply no progress or outside runtime agreement.

## Change

`MachineField` states agreement on each existing machine field.
`Edit.writes` and its frame theorem replace repeated field-preservation proofs.
`RunMachine.dropToken` and `RunMachine.observe` each own their existing write once.
The runtime call sites and proof-side edit interpreter use those definitions.

`PrimitiveProducer` retains actual interpreter results and the returned iteration.
The frame, lexical, and reference consumers use that producer.
Its synchronous constructor retains an operation even when references stay equal.
The old reference theorem alone does not expose that distinction.

`NativeActionScope` retains each spawned child's captured source point.
The source witness does not establish the captured values' generation permissions.
The shared yield clause records every field of the returned iteration.
Timeout LocalSteps now reads the shared clauses at its seven former evaluator reductions.

The new batteries are reachable from `Test/All.lean`.
No existing theorem statement changes in this integration.
`Evidence.json` records the measured headers, source hashes, and line counts.
The header measurement compares source bytes before the first declaration `:=`.
It measures textual stability only.

## Verification

The integration base is `6eb40cccd`.
The source comes from the machine-field and observer commits, plus three reviewed producer patches.
The individual receipts retain their source pins and patch hashes.
The integration build and axiom gate check the combined source.
The first build passes the law library but finds a stale observer reduction in Timeout StateSteps.
The repaired proof unfolds the canonical observer operation.
The final build rechecks the same targets.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws Test.Machine.EditFields Test.Machine.EditMessages Test.Dogfood.Proofs.PrimitiveProducerReader Test.Dogfood.Scenario.Atomic.WriterMachine Test.Dogfood.Scenario.Timeout
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/SharedIntegrationAudit.lean
git diff --check
```

`Build.log` and `Audit.log` retain the exact outputs.
`Audit.lean` names every changed module except the import-only battery root.
`Evidence.json` records the final check results and unchanged checked source hashes.

## Remaining work

The original Timeout numeric history producer remains open.
It needs captured generation permissions, persistent cleanup provenance, and completed loser-join evidence.
The original Workers, QueueWorkers, Atomic, and CallTree obligations remain open.
The next reference-word connector uses the existing producer and shared path relation.

The machine runtime edits owe their reached behavior comparisons at the planned sweep.
The proof-only changes add no behavior obligation.
No generated gate repair or runtime agreement is claimed by this build.
