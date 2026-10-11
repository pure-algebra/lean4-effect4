# Atomic cleanup writer checkpoint

The original cleanup history obligation remains open.
The checked module proves each actual store write's effect on the cleanup count.
It does not yet connect a note's permission to its finalizer start.

Base: `171e4f2e`.
Module: `Test/Dogfood/Scenario/Atomic/Writer.lean`.
Placement: scope-lifetime-finalization, R11, preservation steps of `Atomic.Cleanup.log_debits`.
Consumer: the original `Atomic.cleans_once` clause through `Atomic.Cleanup.cleaned`.

The six source note addresses retain their literal request identities and exact lexical levels.
The actual native note update adds one identity to its selected reference cell.
The actual command law retains other fibers and unfinished commands.
The original observation's count is bounded by the aggregate over the existing reference heap.
The three initial allocations create no cleanup identity at every leading environment.
The daemon refill, request decision and request deposit cannot increase that aggregate.
These facts require no assumption that the selected cell has key two.

The remaining transport must issue permission at `ranFinalizer` and consume it at the note operation.
Dormant finalizer callbacks must carry no active note permission.
The existing registration-history theorem excludes finalizer children and cannot supply that transport.
The shared answer-flow proof uses predicates over existing code and saved frames.
It introduces no new program representation.
No original scenario statement or assumption changes.
No planned goal enters this checkpoint.

Commands:

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic.Writer`: passes, 1058 jobs; writer compilation takes 3.5 seconds.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AtomicWriterAudit.lean`: passes.
- Audit: 63 declarations within `[propext, Quot.sound]`; zero planned goals and zero declarations modulo goals.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AtomicWriterProbe.lean`: passes.

The probe evaluates the actual source address census.
Its output reports six cleanup notes and the separate daemon refill.
It is finite source evidence, not a history theorem or an outside-runtime comparison.
No behavior gate is owed for these proof-only additions.
Borrowed source modules remain outside the commit.
