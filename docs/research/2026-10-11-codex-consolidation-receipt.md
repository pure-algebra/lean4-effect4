# Shared proof consolidations

## Finalizer credits

The existing finalizer statements now use the shared frame-weight proof.
The original Atomic cleanup claim still requires its application log history.

Base: `4bc3efc44`.
Proof head: `e95f009bf`.
The slice changes `src/Effect4/Laws/Machine/FinalizerCredits.lean`.
It preserves every existing theorem name and statement.
It adds the scalar-model connector and removes the repeated pop traversal.

Placement: scope-lifetime-finalization, R11, through `Atomic.Cleanup.log_debits` and `Atomic.cleans_once` in `Test/Dogfood/Scenario/Atomic/Cleanup.lean` and `Test/Dogfood/Scenario/Atomic.lean`.
The weight counts saved selected finalizer frames.
It establishes no progress or host agreement.

Verification:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.FinalizerCredits Effect4.Laws.Program.FinalizerTransfer Effect4.Laws.Program.FinalizerCommands Test.Dogfood.Scenario.Atomic` passes, 1110 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-11-machine-models/codex/FinalizerCreditsAudit.lean` passes.
- The audit checks 120 declarations within `[propext, Quot.sound]`, with zero planned goals or dependencies on planned goals.
- The original `Atomic.cleans_once` remains modulo `Atomic.Cleanup.log_debits`.
- `git diff --check` passes before the proof commit.

`wc -l` measures 155 lines before and 134 after: 21 fewer lines.
The proof diff adds 38 lines and removes 59.
No executable code changes; this slice reaches no behavior gate.
The other original scenario goals remain open as recorded in the goals plan.

Evidence: [build](2026-10-11-machine-models/codex/FinalizerCreditsBuild.log), [audit](2026-10-11-machine-models/codex/FinalizerCreditsAudit.log).

## Finalizer ledger instance

The finalizer command proof and machine edit proofs now use the shared stack ledger.
All 48 existing theorem statements in the three changed modules remain unchanged.
The original Atomic cleanup log obligation remains open.

Base: `fa02d14ab`, including the adjacent L1 landing `0d1acfd87`.
Proof head: `e28a4a60a`.

Changed files:

- `src/Effect4/Laws/Machine/FinalizerBookkeeping.lean` defines the finalizer weight table and exact reading connectors.
- `src/Effect4/Laws/Program/FinalizerCommands.lean` applies the shared command proof and outer edit lift.
- `src/Effect4/Laws/Program/LedgerFinalizer.lean` uses those same connectors.

Placement: scope-lifetime-finalization, R11, through `FinalizerRun.funded_reachable` and `Atomic.cleans_once`.
The instance retains every original distinct-identity premise and native evaluator debit.
The saved-stack ledger does not establish a bound for active code, source-use uniqueness, log provenance, or progress.

Verification:

- The independent L1 integration build, `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.LedgerFinalizer`, passes, 371 jobs.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.FinalizerBookkeeping` passes, 216 jobs.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.LedgerFinalizer Test.Dogfood.Scenario.Atomic` passes, 1113 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-11-machine-models/codex/FinalizerLedgerAudit.lean` passes.
- The audit checks 294 declarations within `[propext, Quot.sound]`; no checked declaration depends on a planned goal.
- The audited unchanged `FinalizerRun` module still declares the existing `once_placed_pushes_once` planned goal.
- The original `Atomic.cleans_once` remains modulo `Atomic.Cleanup.log_debits`.
- A comparison against the base finds all 48 existing theorem statement headers unchanged.
- `git diff --check` passes.

Measured source lines:

| Module | Before | After |
| --- | --- | --- |
| FinalizerBookkeeping | 449 | 348 |
| FinalizerCommands | 318 | 90 |
| LedgerFinalizer | 106 | 86 |
| Total | 873 | 524 |

The source diff removes 349 net lines.
The audit's private command and settlement analysis pattern falls from 16 matches to zero in these modules.
The command instance supplies its evaluator premise and calls the shared proof; it has no command cases.
No executable code changes; this slice reaches no behavior gate.

Evidence: [integration build](2026-10-11-machine-models/codex/LedgerIntegrationBuild.log), [consumer build](2026-10-11-machine-models/codex/FinalizerLedgerConsumers.log), [audit](2026-10-11-machine-models/codex/FinalizerLedgerAudit.log).

## Labelled-word probe

The retained labelled-word probe compiles through `lake env lean`.
It proves shape erasure, composition, event concatenation, and additive balance from local bounds.
Its answer label records input and replacement code.
Its pop label records the actual demand, carried cause, popped frames, selected answer, and emitted events.
The stronger evaluator classification is still open; no library declaration imports this probe.
Its labels do not independently certify source admission or an instance's local weight bound.


## Pop and interference integration

The shared pop and first-lookup proofs pass independent checks after integration.
The original scenario endpoints remain unchanged.

Base: `e2998236e`.
Integrated code head: `7eda5dc76`.
The coordinator adds the `MachinePopTrace` reader to `Test/All.lean`.
The code receipts own their placement, scope, and measured size:
`2026-10-11-codex-stack-consolidation-receipt.md`,
`2026-10-11-codex-worker-entry-receipt.md`, and
`2026-10-11-machine-models/codex/timeout-pop-consolidation-receipt.md`.

Verification uses `LEAN_NUM_THREADS=3` throughout:

- `lake build Effect4.Laws.Program.ReleaseCustody.LoopCommand Test.Dogfood.Proofs.HostTimeoutLoop Test.Dogfood.Scenario.Workers` passes, 1206 jobs.
- `lake build Effect4.Laws.Machine.AnswerFlowCausePop Test.Dogfood.Proofs.MachinePopTrace Test.Dogfood.Scenario.Timeout Test.Machine.AnswerFlow Test.Dogfood.Proofs.HostTimeoutNumberFormFamily` passes, 1145 jobs.
- `lake env lean docs/research/2026-10-11-machine-models/codex/PopIntegrationAudit.lean` audits 203 declarations within `[propext, Quot.sound]`.
- `lake env lean docs/research/2026-10-10-goals-packet/codex/MachineLookupInterference.lean` checks the controls and audits 249 declarations within that allowance.
- The worker research modules compile in order: `MachineWorkersSlots`, `MachineWorkersConnections`, `MachineWorkersNativeSlots`, `MachineWorkersCapturedSlots`.
- Each worker module uses `lake env lean --root=docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/<module>.olean docs/research/2026-10-10-goals-packet/codex/<module>.lean`.
- The same research root checks `MachineWorkersReleaseEntryControl.lean` and `MachineWorkersNativeSlotsAudit.lean`.
- The worker audit checks 215 declarations within the allowance.
- All three audits report zero planned goals and zero dependencies on planned goals.
- `git diff --check` passes.

The worker connection control is synthetic and finite.
It does not establish a reached worker history.
No executable definition changes; no behavior gate is reached.
The logs sit under `2026-10-11-machine-models/codex/` with their integration check names.
