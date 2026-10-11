# Atomic active cleanup writer checkpoint

The actual finalizer start supplies at most one active note reservation.
The actual note exchanges its reservation for one committed cleanup identity.
The whole-history cleanup count obligation remains open.

Base: `9ac218a70`.
Placement: scope-lifetime-finalization, R11, preservation steps of `Atomic.Cleanup.log_debits`.
Consumer: the original cleanup-log history bound and `Atomic.cleans_once`.
Reach: the actual admitted shop, all six requests, arbitrary captured environments and compile fuel.

`Atomic.WriterPhase` reads existing source addresses, code, names and saved frames.
Dormant `.fin` callbacks carry zero active note mass.
Stored program wrappers retain their existing future operations.
The shared `Machine.FrameWeights` law bounds the actual ordered continuation pop.
`native_start` proves the exact native start count and retains the actual heap.
`note_consumes` proves the exact store update and reservation consumption.
Ordinary source edges cannot activate the selected finalizer entry.

`NativeScope.NameAt` now retains the actual producer role for four child-one callback forms.
The producers are bind, catchCause, catchIf and matchCause in `Program.compileEff`.
`Program.interpAt.markCompleted` retains each existing source path.
The control accepts the old child-length field at an onExit parent.
It rejects the synthetic bind callback under the refined role.
No program syntax, machine state or scenario premise changes.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.NativeReplies Effect4.Laws.Program.SourceOpportunityHistory Test.Dogfood.Scenario.Atomic.WriterPhase`: passes, 1090 jobs.
- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic.WriterPhase`: passes, 1077 jobs; final module compilation takes 5.2 seconds.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AtomicCallbackRoleControl.lean`: passes.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AtomicWriterPhaseAudit.lean`: passes.
- Audit: 721 declarations within `[propext, Quot.sound]`; zero planned goals and zero declarations modulo goals.

The first audit rejects an order-derived Nat equality instance reaching `Classical.choice`.
An explicit structural Nat equality instance repairs that proof.
The checked checkpoint establishes local issuance, consumption and stored-frame transfer.
It does not establish the complete writer history, completion or an outside-runtime observation.
No behavior gate is owed for these proof-only changes.
