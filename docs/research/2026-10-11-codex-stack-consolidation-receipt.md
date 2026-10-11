# Native stack consolidation

The merge keeps every existing theorem statement.
It removes the private native stack census.
The shared census adds forward first-lookup survival, which the old backward classification does not establish.

Base: `4bc3efc44`.
Parent: `433137a79`.
Evidence kind: Lean proofs and compiling synthetic controls.
Executable behaviour: unchanged.

## Placement

Concept: reactive-scheduling, invariants over execution traces; scope-lifetime-finalization, R11.
Question: the proposed `command-moves` structure supplies evaluator transport for `ReleaseCustody.Execution.history`.
Reach: every native evaluator and iteration, including machines with duplicate fiber identifiers.
The new update rule requires the actual first lookup.
Limit: this transport proves neither funding, progress, source values, nor writer permission.
Consumers: `NativeStacks.native_links`, `NativeStacks.iteration_links`, `LoopCommand`, and `HostTimeoutLoop`.
The original Workers log obligation remains open.

## Changes

`Interference.lean` extends its existing evaluator census with `LookupEdits`.
`InterferesWithLookup` packages the original classification and first-lookup survival.
All original evaluator interfaces project that one census.
The shared start, countdown, scope-link, and finalizer-fork interfaces also project it.
Their former case proofs are removed.

`NativeStacks.lean` projects stack equality through `StackRegion.other_edits_stack`.
All thirteen original theorem names and statements remain.
The eleven helper names are `map_links`, `spawn_links`, `start_links`, `countdown_links`, `finalizers_links`, and `interrupt_links`.
They also include `action_links`, `frame_links`, `finalizer_links`, `primitive_links`, and `scoped_links`.
`map_links` retains its generic list proof.
Its premise admits arbitrary key-and-stack-preserving functions, beyond the listed other-fiber edits.
It contains no evaluator census.

## Verification

Run from the managed machine-structure worktree with `LEAN_NUM_THREADS=3`.

- `lake build Effect4.Laws.Program.ReleaseCustody.NativeStacks`: passes, 405 jobs.
- `lake build Effect4.Laws.Program.ReleaseCustody.NativeStacks Effect4.Laws.Program.ReleaseCustody.LoopCommand Test.Dogfood.Proofs.HostTimeoutLoop`: passes, 1156 jobs.
- `lake build Test.Dogfood.Scenario.Workers`: passes, 1181 jobs.
- `lake env lean docs/research/2026-10-10-goals-packet/codex/MachineLookupInterference.lean`: passes.
- `git diff --check`: passes.
- The audit checks 249 declarations within `[propext, Quot.sound]`, with zero planned goals and zero declarations modulo goals.

The reader applies iteration transport at actual `Api.load` and `Api.Built` carriers.
The deletion control proves the old backward classification while refuting forward lookup survival.
The duplicate-identifier control proves membership-only replacement while refuting first-record transport.
Both controls concern synthetic states, not admitted histories.
A statement comparison finds all 35 original Interference theorems and all 13 NativeStacks theorems unchanged.

## Measured scope

| Source | Before | After |
| --- | ---: | ---: |
| `Interference.lean` | 504 | 679 |
| `NativeStacks.lean` | 219 | 108 |
| Combined | 723 | 787 |

The combined source grows by 64 lines.
The missing shared lookup guarantee accounts for the growth.
The private NativeStacks evaluator/action markers decrease from eight to zero.
No theorem signature is deleted to improve that count.
No decision lift or scenario history census is added.
No behaviour gate runs because no executable definition changes.

## Remaining work

Workers release registration and release-start bounds remain proved in the coordinator branch.
Workers log identity and debit remain open.
The checked slot and capture producers remain candidate instances for the shared writer model.
This slice makes no claim about their full history propagation.
