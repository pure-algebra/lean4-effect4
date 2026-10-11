# Stored-fiber callback sequencing

The native machine-side sequencing obligation is proved through the shared interference classification.
`ReleaseCustody.Execution.history` remains a planned goal.

Base: `7c69f880`. Head: the commit containing this receipt.

## Placement

Concept: scope-lifetime-finalization, R11, at most once per registration.
Question: the stored-fiber part of `ReleaseCustody.Execution.history`.
Consumer: actual iteration, result installation, and the Workers release assertion.
Reach: every native evaluation and iteration, assuming callback sequencing of the starting stored fibers.
Limits: no command closure, progress, source uniqueness, or host observation follows from this module alone.

`Interferes` now retains each fresh fiber's initialization under the existing word of other-fiber edits.
The initialization stores its program, interruptibility, budget and context.
The spawn proof supplies these from the actual `RunFiber.make` in `Machine.spawn`.
This generic classification does not establish compiled-source ownership or a parent-source relation.
Those remain the source invariant's obligations.

`NativeMachineShape` proves sequencing under each of the three existing other-fiber edits.
A new fiber starts with an empty stack.
The evaluation and iteration theorems then follow from `Interferes`, with no second evaluator case analysis.
`CommandFrames.ofInterferes` projects the retained freshness bound.
`Execution` imports the new consumer module.

## Verification

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.NativeMachineShape Effect4.Laws.Program.CommandFrames Test.Dogfood.Scenario.Workers`: passed, 1143 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/NativeMachineShapeAudit.lean`: passed.
- The audit reports 292 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
- `git diff --check`: passed.

The build and audit logs sit beside this receipt.
The behavior gates remain deferred until the major proof structure lands.
The full admitted-history obligation and the original Workers release goal remain open.
