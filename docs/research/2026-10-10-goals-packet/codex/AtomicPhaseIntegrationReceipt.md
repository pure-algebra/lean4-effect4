# Atomic callback and cleanup integration

Every cleanup identity in the actual admitted histories belongs to the request list.
The count bound against finalizer starts remains open.

Base: `49d2e5ecf`.
Integrated source commits: `ee5629a9c` and `53cb3f53d`, landed as `f4b36bb36` and `6c581ee9e`.
`Test/All.lean` imports `Atomic.WriterPhase` and `Atomic.WriterOwnership`.

Placement: scope-lifetime-finalization, R11, through the original `Atomic.Cleanup.log_debits`.
Reach: actual source callback roles, primitive cleanup writes, and original admitted Atomic histories.
The membership theorem uses the existing native heap history proof.
The writer phase proves local issuance and consumption; it does not yet establish the count bound through history.

`NativeScope.NameAt` now retains the actual constructor roles of four callback families.
Their actual compiler producers supply those roles.
The retained control rejects a synthetic success callback pointing at a finalizer parent.
The compiler, native behavior, and original scenario propositions remain unchanged.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.StackRegionCommands Test.Dogfood.Scenario.Atomic.WriterPhase Test.Dogfood.Scenario.Workers Test.Dogfood.Scenario.Timeout`: passes, 1229 jobs.
- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic.WriterOwnership Test.Machine.MaskBracket`: passes, 1131 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AtomicPhaseIntegrationAudit.lean`: passes.
- Audit: 742 declarations within `[propext, Quot.sound]`; zero modulo planned goals; zero planned goals.

The retained logs record the measured output.
The independent stack-region target in the first build belongs to the adjacent base-law landing.
No behavior gate is owed for these proof-only changes.
