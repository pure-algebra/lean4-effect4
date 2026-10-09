# PartitionedSemaphore bookkeeping production slice

Base: `979be0ad8b86f356dc83aa7f6bdab46228684a32`.
Branch: `codex/partitioned-bookkeeping`.
The owner requests production preparation through concrete modules and shared semantics.
Claude owns the active program splice work in the primary checkout.
The broader organization seat owns the shared analysis design.
This slice changes neither area.

## Contract

Follow decisions rows 330, 331, 333, and 335.
The previous plan is `git:8bb77baa:docs/research/2026-10-08-partitioned-semaphore-plan.md`.
The source is `vendor/effect-4.0.1/src/PartitionedSemaphore.ts`.
The source profile contains finite natural capacities and requests, including zero.
The scalar state holds capacity, available permits, and the total unmet need.
It contains no request identity or partition queue.

The independent model defines initialization, availability, attempted acquisition, and reservation arithmetic.
Initialization sets capacity and availability together, with zero waiting.
An attempted zero acquisition succeeds unchanged.
An excessive acquisition fails unchanged.
An accepted positive acquisition subtracts availability.
Reservation records only the unmet need and zeroes availability.
Its source connector requires insufficient availability and a request within capacity.

The stored steps remain data in the existing Step language.
Deriving supplies the scalar record's type and exact image.
Named fields and inputs supply each source builder.
No new program representation, wrapper, identity encoding, or general analysis service is introduced.

## Proof placement before work

| Obligation | Concept and question | Reach and hypotheses | Exclusions | Consumer and requirement |
| --- | --- | --- | --- | --- |
| Four value equations | `translation-simulation`; helpers of `partitioned-semaphore-bookkeeping` | Each scalar Step evaluates to the independent model; reservation retains its branch premises | Registration, cancellation, delivery, schedules, host execution | Source reading laws; R10 |
| Four reading connectors and their aggregate | `translation-simulation`; `partitioned-semaphore-bookkeeping`, role simulation | Inputs read their exact images; initialization observes its record, availability its count, and updates their replies with next records | Allocation, codec admission, full module agreement, progress | Checked bookkeeping callers and the later waiting model; R10 |
| Four typing connectors | `store-typing`; readers of `step-language-typed` | Inputs have the declared types; the native atom signature holds | Handle validity, codec admission, behavior agreement | Checked Ref callback callers; R4 |
| Public finite controls | Existing claims above | Construction, acquisition boundaries, reservations, and wrong-update controls at public imports | Any universal host or scheduling result | Landing acceptance |

Before proving the aggregate, add its concrete pointer to the semantics registry.
The aggregate collects the four source readings; it states no stronger observation than those readings.
Model helpers need a named consumer in this table or a follow-up proposal.

## Ownership

The implementation agent owns only the new PartitionedSemaphore core and law directories.
The root owns root imports, the semantics registry row, architecture placement, public controls, and integration receipts.
An independent probe agent owns only its retained waiting comparison research files.
The probe compares actual Semaphore and PartitionedSemaphore behavior before proposing shared waiting abstractions.
No agent edits owner rulings, the lakefile, active primary files, or another seat's files.

## Completion

The new core and law modules build through their library roots using narrow targets.
The concrete proof graph pointer resolves and its proof standing contains no open goal.
Each new law has a consumer or an explicit later obligation in the receipt.
Public controls use the same source builders that callers use.
An independent review checks branch premises and the model's separation from the steps.
The scoped axiom check includes generated declarations and checks the core/law boundary.
Record commands, results, source pins, the shared API findings, and remaining wrapper obligations.
Commit explicit paths on the isolated branch.
Run no full sweep and push nothing.
