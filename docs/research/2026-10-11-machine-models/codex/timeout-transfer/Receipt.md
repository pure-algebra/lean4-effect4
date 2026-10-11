# Integrated timeout message and reference proofs

The original stale-reply theorem builds after R2.
The cleanup and retry declarations remain planned goals.
The shared reference transfer supplies actual operation evidence, but not a numeric history by itself.

## Placement and change

Base: `7ecf64e6d41003aaafa52ef1cd55e18efd777961`.
Head: the commit containing this receipt.
Changed source paths and exact bytes: `SourceHashes.json`.
Each path matches the checked agent snapshot.

`MessageReceipt.md` places the message proof under host-session-protocol, R6.
Its consumer is `HostTimeoutHistory.successful_body_seen`, then the original `Timeout.stale_never_applies` theorem.
The observer producer retains one case analysis and supplies actual pending, token, and resume evidence.
The consumer removes its private callback and interrupt-list proofs.

`ReferenceReceipt.md` places command reference transfer under store-typing, R4, and scope-lifetime-finalization, R11.
The sole command analysis produces the shared transfer.
The old heap theorem statements remain unchanged.
The numeric consumer requires the actual captured source point and its permission at the current heap.
Unchanged references alone cannot issue an attempt or cleanup event.

## Verification

The integration branch independently runs:

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.NativeHeapHistory Test.Dogfood.Proofs.HostTimeoutNumberFormFamily Test.Dogfood.Scenario.Timeout
Build completed successfully (1182 jobs).
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/RootTimeoutTransferAudit.lean
#axiom_audit: 371 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
#axiom_audit: 141 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
#axiom_audit: 25 declarations within [propext, Quot.sound], 1 of them modulo planned goals; 2 planned goals
```

The retained command output is `Build.log` and `Audit.log`.
The first audit covers the message slice and its actual history consumer.
The second covers reference transfer and its numeric consumer.
The third covers the scenario, including its unchanged planned goals.
The measured source diff adds 674 lines and removes 265 lines across 10 paths.
`Lines.json` records each path's old length, new length, additions, and removals.
`git diff --check` passes before the commit.

## Boundary and remaining work

This slice changes proofs only.
It adds no executable behavior input and owes no additional behavior comparison.
The R2 behavior sweep remains owed.
The numeric producer must connect actual source permission, captured cells, attempt generation, loser join, cleanup, and returned timeout outcome.
The existing retry and cleanup statements remain unchanged in this slice.
No progress, physical deadline, or general host agreement follows from these proofs.
