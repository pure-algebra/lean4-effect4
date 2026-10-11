# Atomic cleanup identity membership

Every cleanup identity in an actual admitted history belongs to the six request identities.
The finalizer-start count bound remains open.

Base: `ee5629a9c`.
Placement: scope-lifetime-finalization, R11, membership clause of `Atomic.Cleanup.log_debits`.
Consumer: the original cleanup observation and `Atomic.cleans_once`.
Reach: every history at the original compile budget, including incomplete commands and interruptions.

`WriterOwnership.logged_requests` consumes the existing native heap history theorem.
Its cell predicate says every identity outside the request list has zero count.
The actual write-site census retains only the six request literals for note updates.
Allocation, decision, deposit and refill cannot increase any outside identity.
The existing heap invariant carries those facts through complete configuration and decision transport.
The observation reader bounds each logged count by the existing reference-heap aggregate.
The fragment premise follows from the actual built shop.
The empty row table converts the original admitted history to its existing control-history fragment.
No new source or execution carrier, runtime state or scenario premise is introduced.

Commands:

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic.WriterOwnership`: passes, 1093 jobs; module compilation takes 4.3 seconds.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AtomicWriterOwnershipAudit.lean`: passes.
- Audit: 21 declarations within `[propext, Quot.sound]`; zero planned goals and zero declarations modulo goals.

The result proves the membership clause through the actual history endpoint.
It proves no count bound, completion or outside-runtime observation.
No behavior gate is owed for these proof-only changes.
