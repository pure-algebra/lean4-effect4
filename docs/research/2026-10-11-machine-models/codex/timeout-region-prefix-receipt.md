# Timeout region prefix receipt

The connector establishes a saved region after the actual count write.
It leaves the later numeric history and the two original numeric goals open.

## Placement

Concept: scope-lifetime-finalization, R11, and store-typing, R4.
Question: `Timeout.cleanup_keeps` and `Timeout.retries_declared` need the committed attempt count before finalizer execution.
Consumer: `HostTimeoutNumberCounted.count_prefix_region` consumes the shared `StackRegion.drive_from_prefix` law.

`StackRegion.entry_suffix_held` derives the region from the actual looked-up fiber and its exact saved suffix.
`StackRegion.drive_from_prefix` consumes a checked local execution and an allowed remaining command prefix.
It retains the original compiled cut and its ordered base prefix.
`HostTimeoutNumberCounted.attemptRegion` names the actual attempt onExit beneath the count callback.
`HostTimeoutNumberCounted.count_prefix_region` uses the checked count write and that region law.

Reach: the actual Timeout source, native evaluator, accepted row table, symbolic store, cursor and arbitrary remaining command budget.
The premises retain exact heap, saved callback classes, operation budget, lookup, compiled entry and detached evaluation boundary.
The result retains the numeric image and frame at entry, then the region and compiled cut through the permitted remaining prefix.

Limit: the region result supplies no later heap preservation, cleanup completion, retry admission or progress.
The fixed budget compatibility statement remains unchanged because its type explicitly names 1996.
The new producer neither invokes that wrapper nor fixes a remaining budget.
The host boundary remains unchanged.

## Commits and files

Base: `7a8880da0`.
Proof head: `9a28247b1`.

- `src/Effect4/Laws/Program/StackRegionRun.lean`
- `Test/Dogfood/Proofs/HostTimeoutNumberCounted.lean`

The affected files grow from 320 lines to 420 lines.
The slice adds 100 lines and removes zero lines.
It adds no private evaluator or command census.
The actual count consumer now uses `StackRegion` and `LiftPrefix`.

## Verification

Commands run in the host-planned-goals worktree, with one Lake process at a time:

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.StackRegionRun
Build completed successfully (416 jobs).

LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutNumberCounted
Build completed successfully (1101 jobs).

LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutNumberFormFamily Test.Dogfood.Scenario.Timeout
Build completed successfully (1169 jobs).

LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/timeout-region-audit.lean
#axiom_audit: 19 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals

git diff --check
No findings.
```

The independent audit imports and audits both affected modules.
The slice changes no executable definition, generated target or outside comparison input.
No additional behavior gate is reached.

## Next shared transfer

The generated `evaluatePrim.fun_cases` exposes 16 actual branch hypotheses.
They include source code, asynchronous registration state, countdown result, target exit, action selection and synchronous state answer.
An algebra repeating those branches would repeat the eliminator.
The next connector composes `ControlSteps.native_sync_op` with `AnswerFlow.sync_answer` and moves concrete numeric consumers.
It leaves child source, race acceptance and later history premises explicit.

## Original goals

`Timeout.stale_never_applies` remains proved in the integration base.
`Timeout.retries_declared` remains open.
`Timeout.cleanup_keeps` remains open.
The settled retry ruling remains unchanged: retry follows a declared failure returned after selected cleanup completes.
