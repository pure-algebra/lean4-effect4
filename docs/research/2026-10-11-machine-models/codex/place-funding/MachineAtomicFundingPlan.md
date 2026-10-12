# Atomic cleanup funding: placement and shared seam

The next implementation targets the unchanged `Atomic.Cleanup.log_debits` declaration.
The generated-key migration remains pending.

## Placement

1. Concept: `scope-lifetime-finalization`, requirement R11.
   Question: the original Atomic cleanup observation counts at most one write per recorded finalizer start.
   The registry claim remains the original `cleans_once` scenario clause.
2. Proof role: application instance of the existing place ledger.
   The endpoint remains `Atomic.Cleanup.log_debits` in `Test/Dogfood/Scenario/Atomic/Cleanup.lean`.
   `Cleanup.cleaned` consumes it.
3. Reach: the admitted `shop .none`, its existing compile budget, and every actual `Run.HistoryOf`.
   Fuel cuts and interrupted histories remain included.
   No theorem over arbitrary raw commands replaces the history premise.
4. Limits: funding proves the observed count bound, not completion, ordering, or host agreement.
   An open local debit or source permission remains an open premise.
5. Unlock: close the remaining cleanup observation of the original Atomic `cleans_once` claim.

## Existing facts

`WriterOwnership.logged_requests` already proves the membership conjunct on the exact original history.
`WriterMachine.ledger` reads the aggregate cleanup count, active frame reservations, and actual finalizer-start issuance.
`WriterMachine.ledger_funded` exposes that reading without introducing another observation.
`Writer.observe_count_le_heap` bounds the actual observed cell by the aggregate.
No fixed allocation-prefix model is required for this endpoint.

`WriterSync.sync_bound` supplies the actual represented store-operation cost.
`WriterEvaluation.step_bound` supplies the actual frame return cost.
`WriterFinalizers.native_start_bound` supplies the active note allowance at its matching native finalizer start.
`WriterMachine.settle_debit` already consumes `PlaceLedger.install_balanced` and `PlaceLedger.settle_balanced`.

The shared source history supplies `ConfigurationAt`, including actual operation origins and callback source heads.
The fork ledger supplies actual fiber identity uniqueness.
`PrimitiveProducer` retains the actual selected primitive family.
`RefWords.Certified` retains successful synchronous operations and their exact answers.
Shared edit paths retain actual lookups before resolved record writes.

## Exact missing funding obligations

For each `id` in `requests`, the following facts are still needed:

- Initial funding: `(WriterMachine.ledger id).Funded 0 (Api.load b.program budget.compileFuel) [] []`.
- Local native debit: the ledger's `IterDebit` for actual `evaluateNative`, under actual source frame ownership and fiber uniqueness.
- Charged iteration debit: the same bound after run-loop interruption and the forced-yield wrapper.
- Administrative balance: actual command edits retain the state metric and do not increase active reservations beyond emitted start issuance.
- Reply balance: actual prepared answers and scheduled resumes retain that funding under the admitted reply/source evidence.
- History composition: attach the funded fact to the existing source decision lift and induct over the original admitted history.

The original conclusion follows from history funding and `Writer.observe_count_le_heap`.
Its membership conjunct uses `WriterOwnership.logged_requests`.
Each source and bookkeeping premise must be discharged from the original admitted history.

## Gap in the current shared structure

`PlaceLedger` currently shares installation, settlement and arithmetic composition.
It does not supply a full evaluator or command funding fold.
`StackLedger.LedgerRun` supplies that fold only for saved-stack weights.
It cannot read the Atomic state metric or active-code reservation unchanged.

A new Atomic command or evaluator case census would duplicate the completed shared classifications.
The implementation stops before adding one.
The smallest missing shared seam is a place-ledger funding fold consuming those existing classifications.

Its primitive part should consume `PrimitiveProducer`, a frame-weight model, and local source/store transfer premises.
Its command part should extend the existing `LedgerRun` ownership and actual-prefix edit interpretation to active/state places.
The existing stack-ledger endpoints should become zero-state, zero-active instances with unchanged headers.
No second command classification or actual-history carrier should land.

The application supplies actual note costs, dormant-finalizer weight zero, start issuance, and terminal-reply weight zero.
The shared fold supplies execution-family composition and installation order once.
A conditional fold must not be presented as closing the original endpoint until its application premises are proved.

## Other original endpoints

| Endpoint | Shared facts available | Remaining application facts |
| --- | --- | --- |
| Workers `logs_step` | release funding, source ownership, saved answer transport | exact acquired connection identity and captured release entry; writer allowance |
| QueueWorkers `logs_history` | registration uniqueness, release funding | three captured cleanup identities and writer allowance |
| QueueWorkers `jobs_step` | actual queue take/offer laws and native reference transfer | actual encoded-cell/source environment, token custody and model correspondence |
| QueueWorkers `rest_step` | model conservation and rest readers | committed versus withdrawn custody and actual queue wait correspondence |
| Atomic `log_debits` | membership, concrete writer costs, active frame and start bounds, shared settlement | full shared active/state funding fold and discharged native/history instance |

Read-only source snapshot: root `9d7d4e5ef`.
No original goal is claimed proved by this review.
