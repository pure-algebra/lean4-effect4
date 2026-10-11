# Actual reference store transfer receipt

The shared transfer and both instances pass their builds and audit.
The original Timeout build stops at existing R2 adapter failures outside this slice.
The two numeric planned goals remain open.

Base: `125865d206dfedd3434d460010366f4fd136d84b` with coordinator R2 dependencies copied unchanged.
Delivery: checked snapshots, for the coordinator's joint R2 integration.
No executable patch is committed here.

## Placement and reach

Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumers: `HeapSites.heap_sites_keep`, `Timeout.cleanup_keeps`, and `Timeout.retries_declared`.
Proof role: an actual primitive store witness and reference predicate instances.
Evidence status: Lean proofs, audited without planned goals.
Reach: actual native current code, interpreter, and before and after stores.
The numeric instance requires its captured source point and current heap permission.
History must still produce that permission and the count, cleanup, and completed-form order.
The slice establishes no progress or outside-host observation.

`StoreExecution.RefTransfer` relates existing code and stores.
Its unchanged branch retains exact reference equality.
Its synchronous branch retains the actual thunk, absent park, and returned store and value.
`RefTransfer.preserves` consumes only that branch's local source permission.
`primitive_refTransfer` uses the generated primitive eliminator and existing administrative reference laws.

`SourceScope.primitive_heap` keeps its name and statement.
Its old private primitive case proof moves to the shared witness.
Its new proof consumes the source writer law through `RefTransfer.preserves`.
The numeric `reference_primitive_heap` uses the same witness and exact `reference_step_point`.
It supplies no reached-history producer.

## Files

- `src/Effect4/Laws/Program/StoreExecution.lean`
- `src/Effect4/Laws/Program/NativeHeapExecution.lean`
- `Test/Dogfood/Proofs/HostTimeoutNumberState.lean`

The library dependency direction requires the carrier in `StoreExecution`.
`SourceScope` already imports that module.
The classifier stays in `NativeHeapExecution`, which imports `NativeReferences`.
This placement avoids a cycle through `SourceScope`.

Measured module lines: StoreExecution 59 to 85; NativeHeapExecution 154 to 170; NumberState 350 to 380.
The old primitive heap proof has no remaining independent case analysis.
One generated evaluator classification serves its library and numeric consumers.

## Checks

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.StoreExecution Effect4.Laws.Program.NativeHeapExecution`
  passes, 522 jobs.
- The actual consumer build compiles `HeapSites` and `HostTimeoutNumberState`.
  The combined 1166-job request also includes the original `Timeout` scenario.
  It stops at existing `ReleaseCustody` and `HostTimeoutEvaluation` R2 adapter failures.
  Those failures concern the new iteration edit field and countdown plan, not the new reference instance.
- `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/store-transfer-audit.lean`
  audits all three changed modules: 202 declarations within `[propext, Quot.sound]`, zero goals or modulo declarations.

## Shared generated-case repair

A private combined import exposes duplicate generated congruence auxiliaries.
`#check` does not retain them: Lean's `elabCheckCore` uses `withoutModifyingEnv`.
The checked shared `Eliminators` command retains generated cases and actual matcher equalities under `evaluatePrim`.
It uses Lean's matcher metadata, including `withFiber`, and adds no behavioral theorem.
Private NativeExecutor and Guard.ReturnCommands copies import the shared module.
Both rebuild, and their combined import passes.
The independent audit covers 528 declarations within `[propext, Quot.sound]`, zero goals or modulo declarations.
The coordinator owns the shared module and final import edits.

## Remaining goals

`Timeout.stale_never_applies` remains proved by the existing host history proof.
`Timeout.retries_declared` and `Timeout.cleanup_keeps` remain planned goals.
Their producer must connect the actual retry cursor, count cell, cleanup completion, and form-return order.
Fixed compile and command budgets remain part of those original statements.
No arbitrary-fuel or arbitrary-message permission is introduced.

## Joint integration

The later full law build and landing audit pass.
`r2-integration-receipt.md` records their commands, counts, and remaining Timeout adapter obligation.
