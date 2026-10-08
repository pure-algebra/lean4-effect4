# Pool data checkpoint

The six Pool agreement statements and typing statements retain their previous hypotheses.
The remaining operation bodies now translate stored Step data.
The shared list authoring helpers remain a following slice.

Base: ca688ee0, with the coordinator's construction, identity, fold, constructor, tuple, and scope checkpoints.
The branch is `codex/module-pool-data`.
The separate renaming checkpoint is fca76c16.

Changed files: Pool Cell, Data, Steps, and Passes; their Laws Data, Passes, Reading, Steps, Typing, and Ops; Test.Program.PoolData.
Cell factors canonical item and waiter schemas.
Passes holds the independent model equations below the source readers.
Ops changes proof bodies alone.

Placement: Translation Simulation, `pool-steps-agree`, requirement R10.
Carrier image and pass evaluation helpers serve the six unchanged operation agreement statements.
Typing helpers serve the six unchanged operation typing statements, requirement R4.
Scope proofs serve operation construction through `Step.scoped`.
Deferred comparisons require the existing deferred identity capability.
Removal retains the table injectivity premise.
These conditional statements establish no allocation, progress, membership, or host execution claim.

Commands and results:

- `LEAN_NUM_THREADS=3 lake build Effect4.Modules.Pool.Passes Effect4.Modules.Pool.Data Effect4.Modules.Pool.Steps`: passed.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Pool.Passes`: passed.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Pool.Reading`: passed.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Pool.Steps`: passed.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Pool.Typing`: passed.
- `LEAN_NUM_THREADS=3 lake build Test.Program.PoolAgreement Test.Program.PoolSteps`: PoolAgreement passed; PoolSteps stopped at Queue typing's pending scope-argument adaptation.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Pool.Ops Test.Program.PoolData`: Ops passed; finite controls first rejected incorrect expected value syntax.
- `LEAN_NUM_THREADS=3 lake build Test.Program.PoolData`: passed after correcting expected list values and an empty-state fixture.
- `LEAN_NUM_THREADS=3 lake env lean /private/tmp/pool-data-trust.lean`: passed for 680 compiled Pool declarations.

The trust control uses auditedFacts and reachedAxiomsMany.
It rejects unsafe, partial, axiomatic, external, replaced, and bodyless declarations.
It permits only propext and Quot.sound as reached axioms.
The finite battery covers four cells and the listed keys, stamps, leases, and scopes.
It establishes no host result.

One overlapping finite-test build was stopped immediately after detection.
The successful commands above run serially.
The initial Ops check required the coordinator's tuple law checkpoint c88f9bbf.
No production declaration uses a planned goal or `sorryAx`.
Roots, registers, and generated reports remain coordinator-owned.
