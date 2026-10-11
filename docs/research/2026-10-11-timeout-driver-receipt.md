# Timeout native command closure

The original Timeout goals remain open.
This slice closes all eighteen actual command cases and lifts their assertion through every command-loop fuel frontier.
Task, accepted-decision and reached-history closure remain required for the original successful-body clause.

## Placement

Concept: host-session-protocol, requirement R6.
Question: `Timeout.stale_never_applies`, clause four.
Proof role: source and pending-command invariant.
Consumer: task and decision closure, then actual accepted native history.
Reach: the actual Timeout program, fetch table, machine records, commands and arbitrary fuel.
This invariant establishes no progress or outside implementation comparison.
It changes no original statement, runtime field or admission rule.

## Result

`HostTimeoutDriver.command_state` covers all eighteen commands.
`HostTimeoutDriver.drive_state` consumes that closure through the existing `Machine.Lift.driveState_lift`.
The command assertion retains the exact successful-body set while fresh tokens extend its immutable class list.
Race registration restores the accepted exit or parks at its original body token.
Cancellation runs unit cleanup beneath the saved body continuation.
Observers retain actual countdown and race callbacks.
Publication and scratch clearing preserve every other queued owner's saved stack.
Scratch clearing uses the coordinator's `exited_not_owner` law.

## Verification

Base: `68ccced9`.
Head: the commit containing this receipt.
Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutDriver`.
Result: success, 1123 jobs.
Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean`.
Result: 1140 existing declarations and 209 new declarations within `[propext, Quot.sound]`.
Both audit groups report zero planned goals and zero declarations modulo planned goals.
No outside implementation comparison runs in this proof-only slice.
The coordinator owns the behaviour gates.
No push runs.

Changed files:

- `Test/Dogfood/Proofs/HostTimeoutLoop.lean`.
- `Test/Dogfood/Proofs/HostTimeoutObservers.lean`.
- `Test/Dogfood/Proofs/HostTimeoutRaceCommands.lean`.
- `Test/Dogfood/Proofs/HostTimeoutCancellation.lean`.
- `Test/Dogfood/Proofs/HostTimeoutExitCommands.lean`.
- `Test/Dogfood/Proofs/HostTimeoutAdminCommands.lean`.
- `Test/Dogfood/Proofs/HostTimeoutDriver.lean`.
- `docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean`.
- This receipt.

## Dependencies

Coordinator modules remain byte-for-byte checking dependencies, excluded from this commit.
The earlier sixteen hashes remain in `docs/research/2026-10-11-timeout-command-custody-receipt.md`.
The following additional copies support the coordinator's `NativeStacks` module.

| Path | SHA-256 |
| --- | --- |
| `src/Effect4/Laws/Program/ReleaseCustody/NativeStacks.lean` | `bb5abd40f8a647bc95d9045c8228c83ef5aaa7613a788faaacb3827d595f250e` |
| `src/Effect4/Laws/Program/ReleaseCustody/NativeSequencing.lean` | `eee6d483b534deefe99e16d35f8d84cda45609534f7ca58d2447d7862c505b2e` |
| `src/Effect4/Laws/Program/ReleaseCustody/RuntimeShape.lean` | `4b49bc72659e86768d2550770a72f6ee9e425b6b61f76e56466b7b53654e35fc` |
| `src/Effect4/Laws/Program/ReleaseCustody/FrameSequencing.lean` | `e43a76e7912495e1d426d9d0da15a8e4b04ec75fca5d66f8947fafd7f83ada92` |
| `src/Effect4/Laws/Program/ReleaseCustody/PopSequencing.lean` | `78149be79c27592f52eb15e9e662b3c5b59172d6e5458996ceeb47e584c3f923` |
| `src/Effect4/Laws/Program/NativeEvaluation.lean` | `ee5542e993363b2ac347c84ee10b77275fcd0da2ca465372e22874756a54be00` |
| `src/Effect4/Laws/Program/NativeConfiguration.lean` | `599d2d13d80b4df9a87a46aed523f81f3cdb785b5fc14709def89ae96da76832` |
| `src/Effect4/Laws/Program/NativeFrameScope.lean` | `d35111868e05ddf64c53658fb20c066aa87f2c667a36fe16d356b64fb72575d7` |
| `src/Effect4/Laws/Program/NativeInterpScope.lean` | `f7c6e3ae6f20dfb98e3e30fea87ca51261124ca77e86835e58c7b8ccf33a1a38` |
| `src/Effect4/Laws/Program/NativeCallbacks.lean` | `0e3260002bae35e7e977110715c63503ee2e824590a61260e75e5e1a1dc4415a` |
| `src/Effect4/Laws/Program/NativeStoreScope.lean` | `baca5ccd41fbc0d9a14f84f3a0f3f03e2073e42890ce44858e2d42c3e2d55579` |
| `src/Effect4/Laws/Program/NativeScope.lean` | `25af9510fec98ec040086384b0758e2c01f5b8ac45b516aa904fd892956539fe` |
| `src/Effect4/Laws/Program/ScopeFragment.lean` | `db3f6c300a58d989a9b2b93b3b241d8883b7a9325c535c5b959c6c3490facce1` |
| `src/Effect4/Laws/Program/SourceScope.lean` | `612b15d8506367d80f5e4372c808b37d5979595ce11651a72076a6e0b133f2bf` |
| `src/Effect4/Laws/Program/StoreExecution.lean` | `236ae75d538423d5c2de521c732fcc8b5ef767f3ab7525774a7155148f021b20` |
| `src/Effect4/Laws/Program/SourceOrigin.lean` | `70a4394e05bea0a8d2be4593f82b6bb329b1d5951673d72a2ff101a3b7f7d991` |
| `src/Effect4/Laws/Program/NativeActionScope.lean` | `e090af39ff5167175de260eb69d5c2d21be6c2587c8054fbd3ec843e48805529` |
| `src/Effect4/Laws/Program/NativeScopeStore.lean` | `2d774673e9460d3d5c20b476eb1c3df011c06a349575c9a03eb9e7c678bd240f` |
| `src/Effect4/Laws/Program/NativeHeap.lean` | `2f7e6429545dfbbf49a6d3e31e7915070f1df99db27aeec58e5e530b235a90fb` |
| `src/Effect4/Laws/Program/HeapSites/Core.lean` | `9e62f20cb7d1440609cb1df5533f9ccba78b76fc14317d5397dc8c099d04d90b` |

The unrelated RaceFirst edit and KernelRfl helper remain excluded.
