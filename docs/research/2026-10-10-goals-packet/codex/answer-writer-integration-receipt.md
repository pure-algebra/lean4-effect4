# Native answers and writer integration

The application proofs now consume actual source callbacks and writes; their complete history obligations remain open.

Base: `3f81a9917`.
Integrated commits: `145389f26`, `8e49f460d`, and `d8c95167f`.
The commit containing this receipt records the integration head.

Concepts: store-typing, R4; scope-lifetime-finalization, R11.
Consumers: Atomic log debits, Timeout cleanup and retry, and Workers log history.

The Atomic slice transports writer reservations through actual compiled sources, callbacks, suspensions, loops, and saved frames.
The Timeout slice connects numeric callback equations to actual native writes and saved answer classes.
The Workers slice checks forced yields, both acquired literals, effective captured cleanup destinations, and one actual cleanup command.
`Test/All.lean` reaches the new Atomic and Timeout modules through their terminal consumers.

## Verification

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic.WriterFrames Test.Dogfood.Proofs.HostTimeoutNumberFlow Test.Dogfood.Scenario.Atomic Test.Dogfood.Scenario.Timeout` passes, with 1212 jobs.

The Atomic audit reports 520 declarations within `[propext, Quot.sound]`, no planned goals, and no declarations modulo goals.
The Timeout audit reports 136 declarations within the same ceiling, no planned goals, and no declarations modulo goals.

The Workers reader build compiles `MachineWorkersSlots`, `MachineWorkersConnections`, and `MachineWorkersExclusivity` with the packet directory as its Lean root.
Its combined audit reports 216 declarations within the same ceiling, no planned goals, and no declarations modulo goals.
The retained audit sources give the exact module lists.
The adjacent build logs and audit outputs retain the command evidence.

## Remaining obligations

Atomic still needs actual primitive, native action, command, and history composition for its writer allowance.
Timeout still needs complete saved-finalizer instances and the original fixed-budget history producer.
Workers still needs source-value and current-frame propagation through its complete admitted history.
These conditional symbolic proofs establish no runtime agreement or progress.
The proof-only integration reaches no behaviour gate.
