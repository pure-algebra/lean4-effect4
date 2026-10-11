# R2 queue transport

The queue settlement and native assembly proofs pass their narrow builds.
The whole Laws build remains pending.
The public queue endpoints acquire no new premises.

Base and current committed head: `b4dcef4f1`.
Status: uncommitted integration work.
Evidence kind: compiling proofs and a focused axiom audit.

## Placement

Concept: reactive-scheduling, R11, through the reachable guard-token ownership claim.
Consumers are `guardQueue_settle_rest`, `guardQueue_settle`, and their actual native assembly.
The existing `OtherEdit.controls` observes running or exited fibers.
`OtherEdits.controls` composes that observation through the existing relation.
The old interpreter interruption law becomes a fresh-cause adapter.
`Messages.commandControls_fiberEdits` uses the shared lookup witness.
It adds no command, evaluator, or message case analysis.

## Internal statement boundaries

`ControlsAway` previously froze current code on idle, unparked fibers.
An interruption may change that code and schedule its evaluation.
Commands read current code only on running, unparked fibers.
The relation now covers running-unparked or exited fibers.
Its consumers retain their original queue claims.

Raw settlement may lack the selected owner.
Nonempty messages then lead to a halt and an empty command list.
The old precise `settle_commands_rest` equation therefore receives an owner-retention premise.
`settle_commands_rest_cases` covers either halt or prefix-plus-tail without that premise.
Actual queue proofs use the general disjunction.
The retained finite controls check both raw boundaries.

## Shared structure

`Edits.settle_keeps` supplies the queue's token and race projections.
It also replaces the private settlement field proof in `FiberSumMessages`.
The queue uses the same installed owner, message interpretation, and current-owner disposition as the machine.
Messages introduce no external request, so the existing reservation relation survives.

## Changed modules

- `Program/Interference`.
- `Program/Guard/{Core,Messages,RegistrationQueue,FinishQueue,SettleQueue,NativeQueueTail}`.
- `Machine/FiberSumMessages` consumes the agent's shared `Machine/EditWords` frame rule.

These paths are under `src/Effect4/Laws/`.
The `NativeQueueTail` change only uses the general command-tail disjunction.
Its dependency build passes with the repaired native producer.

## Checks

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Guard.SettleQueue Effect4.Laws.Machine.FiberSumMessages` passes with 390 jobs.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/R2QueueTransportAudit.lean` passes.
The audit reports 1,008 declarations within `[propext, Quot.sound]`.
It reports zero planned goals and zero declarations modulo planned goals.
The saved audit source and output accompany this receipt.

`git diff --check` passes at this checkpoint.
The whole Laws build remains a required integration check.
The machine change cannot commit before that build passes.

## Limits

These facts establish no source completeness, progress, liveness, or new host correspondence.
The original numeric producer goals remain open.
Behaviour gates remain scheduled after the major structures land.

## Joint integration

The later full law build and landing audit pass.
`r2-integration-receipt.md` records their commands, counts, and remaining Timeout adapter obligation.
