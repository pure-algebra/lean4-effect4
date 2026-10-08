# Named Semaphore authoring receipt

All five live pure operation bodies use named step inputs.
Their source applications use the same input declarations.
The module retains existing public operation signatures and proof statements.

The base is `b024f2ef`, including named inputs, list builders, record aliases, and shared option laws.
The changed files are `src/Effect4/Modules/Semaphore/Data.lean`, `src/Effect4/Modules/Semaphore/Steps.lean`, and `src/Effect4/Laws/Modules/Semaphore/Data.lean`.

## Authoring

`CountInputs`, `TakeInputs`, `VisitInputs`, and `WithdrawInputs` own input names and types.
`step_inputs%` supplies each live body's step variables.
`input_sources%` orders each public step's source arguments from those declarations.
`input_ref%` supplies transparent compatibility witnesses for unchanged proof consumers.
No compatibility witness repeats a positional index.

`removeWith` accepts a Step operand and uses shared `Lists.removeBy` with `item_step%`.
`fromFirst` uses `fold_step%` and captures the derived available-count step.
`waiter` uses `record_step%` against the canonical waiter schema.
`freeValue` accepts a cell Step operand.
The older Input-valued interfaces remain transparent bridges to those operands.

`remove_eval` applies the shared `Lists.eval_removeBy` connector.
The module no longer repeats the removal fold's value proof.
The remaining module equations retain their independent model and existing assumptions.

## Placement and boundary

The equations continue to serve `semaphore-steps-agree`, under `translation-simulation` and R10.
Their consumers remain the existing step agreement and store-attempt statements.
Typing and scope continue through the shared Step laws under R4.
Named metadata establishes neither type formation nor identity validity.
No result establishes wrapper scheduling, cancellation, liveness, or native compatibility.

## Checks

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Semaphore.Ops Test.Program.SemaphoreData Test.Program.SemaphoreAgreement Test.Program.SemaphoreOps Test.Program.SemaphoreScenarios Test.Program.StepInputs` passes with 906 jobs.
`LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-semaphore-trust.lean` passes.
The nine audited public agreement, typing, and scope consumers depend only on `[propext, Quot.sound]`.
`git diff --check` passes.
Root imports and the full battery remain coordinator work.
