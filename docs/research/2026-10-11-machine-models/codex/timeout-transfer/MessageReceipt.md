# Timeout message transport after R2

The original stale-reply statement stays unchanged.
The retry and cleanup goals remain open.
The slice repairs the source assertion after addressed messages replace producer-held fiber writes.

## Placement and scope

Concept: host-session-protocol, R6.
Claim: `Test.Dogfood.Scenario.Timeout.stale_never_applies`, including its successful-root clause.
Consumer: `HostTimeoutHistory.reached_state` and `successful_body_seen`, then the original scenario theorem.
The source assertion retains actual native code, saved callbacks, token classes, and reference outer shapes.
It covers every recorded host row and every scenario script.
It establishes no numeric write order, retry bound, cleanup progress, or physical deadline.
The host boundary stays unchanged.

## Shared structure

`EditObserverWords.observer_producer_path_metadata` owns the existing observer producer analysis.
It adds exact pending predecessors, tokens, resume modes, observer equality, exit equality, and child inclusion.
Its observe hook retains equality with the original observer.
Its countdown command hook retains the token equality from the actual pending lookup.
The original `observer_producer_path` keeps its exact header and discards these extra facts.
No second observer analysis remains.

`HostTimeoutStateSteps.configuration_messages` consumes the existing edit path and its actual prefixes.
Addressed interruptions read the current stored fiber.
Actual countdown production returns its admitted observer message separately from the local returned fiber.
The existing primitive analysis returns that message permission alongside its previous source assertions.

`HostTimeoutSettle.settle_state` installs the local fiber, applies the admitted message word, and reads the owner again.
It transports saved-stack demands through `InterferesWithLookup.backward_lookup` and `StackRegion.other_edits_stack`.
The outcome proof retains its previous argument list as `settleOutcome_state`.
The original `settle_state` statement stays unchanged.

`HostTimeoutObservers.countdown_observer` consumes the shared producer path.
Its former private callback proof is removed.
The retained `interrupt_each_evaluates` and `pending_progress_fiber` declarations become shared-law adapters.

## Files

- `src/Effect4/Laws/Machine/EditObserverWords.lean`
- `Test/Dogfood/Proofs/HostTimeoutStateSteps.lean`
- `Test/Dogfood/Proofs/HostTimeoutParkSteps.lean`
- `Test/Dogfood/Proofs/HostTimeoutLocalSteps.lean`
- `Test/Dogfood/Proofs/HostTimeoutSettle.lean`
- `Test/Dogfood/Proofs/HostTimeoutObservers.lean`
- `Test/Dogfood/Proofs/HostTimeoutRaceCommands.lean`
- `Test/Dogfood/Proofs/HostTimeoutCancellation.lean`

## Dependency fence

Working branch head before this slice: `125865d206dfedd3434d460010366f4fd136d84b`.
Coordinator R2 runtime and proof dependencies are copied for checking and excluded from this proof patch.
Coordinator landing: `b7ba5891a`, integration base `68f3808d`.
The exact shared backward reader comes from `6c4bb709d`.
Its copied `Interference.lean` has SHA256 `01980e796dfdc1b16f0d363e5c8ecc5e5f3b03fc7438d87fe5e295f71531f75c`.

## Verification

Commands use `LEAN_NUM_THREADS=3` and one Lake process at a time.
The initial endpoint build exposes `Classical.choice` through `List.eq_nil_iff_forall_not_mem` in the new metadata helper.
The repair uses constructive list cases.
The first three message modules pass an independent audit of 135 declarations with zero goals or declarations modulo goals.
Final original endpoint and full slice checks follow the repair.
No executable source changes in this slice.
No outside behavior input changes, so no behavior gate is reached.

## Remaining original work

`Timeout.retries_declared` and `Timeout.cleanup_keeps` remain planned goals.
Local reference equations do not produce the numeric history invariant.
That invariant must couple the retry cursor, captured cells, committed count, cleanup completion, and selected form outcome.
The fixed scenario budgets remain part of those original statements.
No arbitrary-fuel entry phase or repeated raw count write becomes an admitted history premise.

Final checks:

```text
LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Timeout
Build completed successfully (1139 jobs).
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/timeout-r2-original-audit.lean
#axiom_audit: 373 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The audit covers the shared observer module, all seven changed Timeout proof modules, and the actual history endpoint.
`git diff --check` passes for those seven proof files.
The original scenario theorem passes its plan gate.
Its unchanged retry and cleanup declarations remain planned goals.

Measured lines, before and after:

| Module | Before | After |
| --- | --- | --- |
| `EditObserverWords` | 380 | 449 |
| `HostTimeoutStateSteps` | 394 | 483 |
| `HostTimeoutParkSteps` | 320 | 335 |
| `HostTimeoutLocalSteps` | 384 | 403 |
| `HostTimeoutSettle` | 173 | 244 |
| `HostTimeoutObservers` | 178 | 175 |
| `HostTimeoutRaceCommands` | 206 | 208 |
| `HostTimeoutCancellation` | 100 | 101 |

The observer producer keeps one analysis.
The Timeout observer consumer removes its old callback analysis and interrupt-list recursion.
Message permission and actual post-message lookup supply the remaining added proof structure.

The explicit proof patch is `/private/tmp/timeout-r2-message-proofs.patch`.
Its SHA256 is `1f23164a34339deacd1b1fb2ecfdda9e199f5aa78449a50acd4d8c6cc78f7503`.
The adjacent hash table records exact coordinator baselines and checked snapshots.
No copied runtime or unrelated dependency file belongs to this patch.
