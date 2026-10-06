# Pool contract card — proposed

Status: design input for the coordinator. Neither the profile nor these obligations are ratified.
Evidence: pinned-source inspection at `d3a3e558`; finite Python branch mirrors only.

## 1. Source

Read `makeWithStrategy`, `get`, `getSlowWith`, `leaseItemBookkeeping`, `releaseItem`, `wakeWaiters`, `allocate`, `invalidatePoolItem` and `shutdown`.
They live in `vendor/effect-4.0.0-rc.112/src/Pool.ts` and `vendor/effect-4.0.1/src/Pool.ts`.
The version differences in `review.md` prevent an unnamed common profile.

## 2. Operations and first profile

Candidate: fixed positive size, per-item concurrency one, scoped `make` and `get`, and scope-driven lease return.
An authoring helper can wrap a checked body in a borrowed scope using existing Eff builders.
It need not store a host callback.

Exclude TTL, variable minimum/maximum, custom strategies, `invalidate`, `reserve` and arbitrary native callbacks from this first API.
Keep acquisition failure, caller interruption and pool shutdown in the lifecycle design; they cannot disappear behind those exclusions.
A narrower proof over successful acquisitions must state that premise explicitly.
Excluding public invalidation does not erase failed-acquisition cleanup.

## 3. State and identities

Keep pool identity, item identity, resource identity, lease identity and cleanup-registration identity distinct.
Keep an ordered available-item list and an ordered waiter list.
Each item records its acquisition exit, acquisition scope, borrow count and retirement state.
Each lease records the item and its return obligation.
The pool scope owns creation tasks and item cleanup; the borrower's scope owns the lease return.
Start with empty items and registrations; acquisition populates them.

## 4. Atomic boundaries and cleanup

A lease commits when bookkeeping increments the selected item's borrow count.
Hook installation must share the required protected boundary with that commit.
Waiting registers one removable callback. Cancellation withdraws that registration.
A posted wake selects a fixed counted list at task execution, then delivers to that list.
A notification reserves nothing. A resumed borrower checks state again.

A healthy return decrements the borrow count and restores availability.
An invalidated last return may destroy the item; the wider API must preserve this distinction.
Failed acquisition closes its own scope, including resources acquired before failure.
A live cleanup frontier retains the return or destruction obligation.
It is not a completed cleanup receipt.

## 5. Representation and context

A natural identity can name each allocation; equal resource values need not identify equal allocations.
Target resource identity requires a correspondence with host object identity where that identity is observed.
The acquisition is retained Eff code with typed captures and a declared service-context policy.
Its acquisition scope is distinct from each borrowing scope.
Retain the native numeric profile; do not silently support fractional or negative capacity.
No clock claim is needed while TTL is excluded.

## 6. Public observation

Observe returned resource identity, operation exit, allocation attempts, lease returns and finalization identities.
Also observe waiter registration, cancellation, notification order and live cleanup frontiers for the agreement controls.
Do not expose internal linked-list fields as a public API.
Resource reuse order remains observable when resource identity is observable.

## 7. Reuse and gaps

Reuse `Api.Author.build`, minted Ref callbacks and the existing scope and Deferred operations.
Reuse `step_updates` and `step_keeps_cell` from `Laws/Modules/Queue/Steps.lean` at their actual premises.
Reuse `indexed_ref_step_preserves` and `termMaps_of_typed` for typed state and captured terms.
Move a helper only when the second concrete consumer uses its unchanged statement.

R7's retained-behavior contract is an immediate prerequisite for a reusable acquisition provider.
Row 260 excludes native `releaseAll`; Pool shutdown therefore needs a named replacement contract or an explicit later extension.
A fresh counter/Deferred completion protocol is only a candidate, not established native agreement.

## 8. Proposed placed obligations

These are proposed subclaims of R10's existing composed-module expansion obligation, `Agrees profile module expansion`, under decisions row 79.
They serve that owner rather than create an independent claim family.
R8 applies later to the target-facing equal-observation connection; an atomic model-step theorem does not establish it.
R4 already requires the cell invariant, operation typing and preservation at the admitted state types.
Each module supplies those existing obligations through the checker and store lemmas; this card adds no separate typing theorem.

| Claim and role | Placement and consumer | Property, premises and observation | Exclusions and prerequisite |
| --- | --- | --- | --- |
| `pool-step-agrees`, module goal | `translation-simulation`, R10; Pool atomic steps | Decoding a well-formed cell after one admitted step equals the independent transition and ordered notifications | No wrapper or progress; selected version and model first |
| `pool-lease-return`, lifecycle goal | `scope-lifetime-finalization`, R11; scoped get | A committed lease owns one return registration; completed return decrements that lease once; healthy return retains its resource | No whole-run exactly-once claim; masked hook connector and identity invariant first |
| `pool-wake-snapshot`, scheduling helper | `reactive-scheduling`, R12; posted Pool wake | At task entry, select the first bounded callbacks, then deliver exactly that fixed sequence under cancellation rules | No reservation or fairness; driver budget covers reached receiver continuations, or retained driver suspension |
| Retained acquisition specialization | `residual-program-typing`, R7; allocation | Resolved Eff acquisition stays typed at its declared result/error types under capture and service-context premises | Conditional until `resolve_typed` and lifetime premises are supplied |

## 9. Positive and deliberately wrong controls

- Return a healthy lease, borrow again, and observe no resource finalizer between the borrows.
- In a later invalidation extension, hold two leases; the first return keeps the item, and the last return finalizes it.
- Fail acquisition after registering cleanup; observe that cleanup without pool shutdown.
- Select A and B; let A's resumed code register C or withdraw B; compare against a live-scan mutant.
- Post a wake, then register a waiter before task execution; reject a snapshot taken too early.
- Stop during cleanup and retain the frontier; reject a report that labels it completed.

## 10. Choices for the owner

Choose the source version and observable reuse order.
Choose the shutdown contract that fits the excluded `releaseAll` operation.
Choose the admitted acquisition/capture profile and its context policy under R7.
These decisions precede implementation; they do not delay unrelated approved work.
