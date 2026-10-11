# Actual failure selection and interrupted handlers

The saved contract now explicitly covers interrupted handler discards, without admitting arbitrary causes at later cleanup stages.

Base: `ca2237d48`.
Integrated application checkpoints: `e3735494e` from `f07917a07`, and `327de3402` from `0e7167109`.
The landing commit records the head and changed paths.

## Placement

Concepts: store-typing, R4; scope-lifetime-finalization, R11.
Consumers: Workers log history, Timeout cleanup ordering, and native finalizer interception.

`SavedAt` retains its existing representation and gains an explicit discard clause.
That clause requires a real failure arm, an interrupted hook result, and the actual `skippedCause` equation.
Its result establishes the older stack's cause class in the same permitted world.
`stack_mono` still transports the same ordered contract.
The change introduces no additional stack relation, evaluator, or stored program representation.

`AnswerFlowCausePop.lean` follows the existing failure pop through missing arms and discarded handlers.
It retains the cause actually carried into the selected frame and that frame's older suffix.
The actual cause-resume consumer invokes the selected arm without a supplied exit.
The native finalizer consumer uses the actual delivered failure exit.

Protected finalizer hooks cannot satisfy the interrupted-handler premise.
Both Timeout source finalizer constructors consume that checked fact.
The cleanup merge wrapper discharges its discard clause from its empty admitted failure class.
The native reader exercises an interrupted handler, a mask, and the selected remaining handler.

## Verification

`LEAN_NUM_THREADS=3 lake build Test.Machine.AnswerFlow Test.Dogfood.Proofs.HostTimeoutNumberCounted Test.Dogfood.Scenario.Timeout` passes, with 1159 jobs.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AnswerFlowCauseAudit.lean` passes.
It reports 338 declarations within `[propext, Quot.sound]`, no planned goals, and no declarations modulo goals.

The Workers reader build recompiles `MachineWorkersSlots`, `MachineWorkersConnections`, and `MachineWorkersExclusivity` against the strengthened shared contract.
Its combined audit reports 246 declarations within the same ceiling, no planned goals, and no declarations modulo goals.

The adjacent logs retain the exact results.
`Test/All.lean` now reaches the counted Timeout entry through `HostTimeoutNumberCounted`.

## Remaining obligations

The original scenario histories must still produce their current-code, store, and saved-stack premises.
Replacement and deferred causes retain explicit admissibility obligations.
The original Timeout retry and cleanup goals remain open.
The original Workers log-history obligation remains open.
This proof-only landing reaches no behaviour gate and establishes no progress or runtime agreement.
