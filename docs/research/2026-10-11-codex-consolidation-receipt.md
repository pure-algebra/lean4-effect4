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
