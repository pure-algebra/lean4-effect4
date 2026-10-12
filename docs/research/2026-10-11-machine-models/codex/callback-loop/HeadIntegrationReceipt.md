# Shared current-head integration receipt

The shared frame proof and both actual consumers pass the integration checks.
Pure frame execution remains distinct from executed native store operations.

## Placement

Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: HeapSites.heap_sites_keep and the original Timeout numeric history claims need actual current-head permission.
Consumers: NativeFrameScope.frame_step_at, NativeEvaluation, and TimeoutReadyEntryProbe.form_entry.
Reach: the existing instruction, present store, ordered saved path, and actual return producers.
HeadAt is proof evidence indexed by the existing Prim instruction.
It introduces no executable evaluator or stored program representation.
The native sync branch still consumes PrimitiveProducer's actual result.
Reached ownership, completed cleanup, and public command room remain open.

## Changes and retained statements

Base: 722f90131e8b69942572084e63c5d7b70134d7fa.
AnswerFlowHead contains the shared contract and frame-step theorem.
NativeFrameScope supplies its existing lexical source facts as an instance.
Its original frame_step_at now consumes the shared theorem.
The actual Timeout Ready form consumes the same theorem at its onExit push.
Waiting and settlement statements remain unchanged.
The header comparison retains all 42 existing named headers across the two replaced files.
HeadIntegrationEvidence.json records exact source and evidence hashes.
The independent outer-history changes belong to a separate slice.

## Checks

The native and Timeout dependency build passes 1143 jobs.
All five affected concrete readers pass against that build.
They cover Ready entry, race ownership, waiting, cancellation, and settlement.
The four-module audit passes 328 declarations within [propext, Quot.sound].
It reports zero planned goals and zero declarations modulo goals.
The whitespace check passes.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.NativeEvaluation Test.Dogfood.Proofs.HostTimeoutNumberCounted
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-11-machine-models/codex/callback-loop/CheckHeadIntegration.py
python3 docs/research/2026-10-11-machine-models/codex/callback-loop/HeadHeaders.py
```

The retained build and reader logs record the results.
HeadAgentReceipt.md retains the earlier isolated checks and their scope.
No executable behavior changes, so no behavior gate runs.
Timeout.retries_declared and Timeout.cleanup_keeps remain planned goals.
