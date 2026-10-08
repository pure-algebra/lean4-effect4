# Semaphore step migration receipt

All five public pure steps now translate `Step` data.
Their existing agreement, typing, and scope statements retain their hypotheses and conclusions.
The independent model and public operation definitions stay unchanged.

The base is `81038823`, including the shared construction, identity, fold, triple, and scope checkpoints.

## Changed files

- `src/Effect4/Modules/Semaphore/Cell.lean`
- `src/Effect4/Modules/Semaphore/Data.lean`
- `src/Effect4/Modules/Semaphore/Steps.lean`
- `src/Effect4/Laws/Modules/Semaphore/Data.lean`
- `src/Effect4/Laws/Modules/Semaphore/Steps.lean`
- `src/Effect4/Laws/Modules/Semaphore/Typing.lean`
- `src/Effect4/Laws/Modules/Semaphore/Ops.lean`
- `Test/Program/SemaphoreData.lean`

## Placement

The carrier equations serve `semaphore-steps-agree`, under `translation-simulation` and R10.
`take_eval`, `withdraw_eval`, and `visit_eval` connect the independent transitions to the data interpretation.
Their consumers are the existing public step agreement statements.
The module encodes its state once at `Leaves.deferredKeys` through `cellC`.
`cellVal_image` connects that encoding to the stored cell.

`remove_eval`, `without_image`, and `withoutC_renew` support the take and withdrawal equations.
`fromFirst_eval` and `visitReply_image` support the visit equation.
`request_equal` connects deferred handle comparison to model numbers under `Table.Injective`.
It establishes neither allocation validity nor store membership.

The three migrated typing proofs apply `Step.typed_of_normal`.
They serve the existing `step-language-typed` consumers under `store-typing` and R4.
The public scope proofs apply `Step.scoped`.
They serve `operation-data-scoped` and application authoring admission under R4.

## Boundary

The canonical `waiterRecord` owns field order.
The new waiter construction follows that order, so its emitted tree differs from the old raw construction.
The proofs use reading and carrier equations rather than false definitional equality.

Legacy raw helper builders and their reader statements remain available.
Some reader statements quantify arbitrary values for fields that indexed steps require to contain natural numbers.
Their unchanged statements cannot become indexed-step corollaries through an unrestricted raw-value escape.
The five public steps use data independently of those legacy helper implementations.

These results establish neither wrapper scheduling nor cancellation, progress, liveness, or native compatibility.

## Checks

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Semaphore.Ops Test.Program.SemaphoreData Test.Program.SemaphoreAgreement Test.Program.SemaphoreScenarios` passes with 890 jobs.

`LEAN_NUM_THREADS=3 lake build Test.Program.SemaphoreOps Test.Program.SemaphoreRelation` builds `Test.Program.SemaphoreOps` successfully.
The combined command fails on the existing Queue `sizeStep_typed` call, before the relation reader builds.
The Queue seat owns that shared-API application repair.

`LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-semaphore-trust.lean` passes.
The nine audited agreement, typing, and scope consumers depend only on `[propext, Quot.sound]`.
`git diff --check` passes.

The new finite controls use populated states and actual deferred keys.
An aliasing-table control distinguishes handle equality from model-number equality.
No check invokes a native host.
The root imports, relation reader after Queue repair, and full battery remain coordinator work.
