# Queue cleanup source and release accounting

Concept: scope-lifetime-finalization, R11.
Question: the unchanged `QueueWorkers.releases_once` consumes `Assertions.cleanup_step`.
The shared source-opportunity history proves registration uniqueness.
The shared release-custody history bounds release starts by those registrations.

Check the actual queue source at every job total.
Its acquisitions must lie outside repeated loop bodies and finalizer bodies.
Its scopes must be sequential, and its source must contain no race action.
Then apply the existing history theorems with the original source paths and admitted-history carrier.

Replace the internal cleanup decomposition with those proofs and one explicit log-debit goal.
The log goal retains the actual history and concrete observed cell.
It must prove identity membership and the count bound against release starts.
The original application statement and its budget and script scope stay unchanged.

This landing establishes neither log provenance, job conservation, queue rest, nor progress.
It adds no evaluator case census or execution representation.
Build the source module and QueueWorkers consumer, then audit the changed modules.
