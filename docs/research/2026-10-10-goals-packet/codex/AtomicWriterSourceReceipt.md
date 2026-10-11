# Atomic source writer transport receipt

The source and saved-frame writer bounds pass together.
The original numeric cleanup-log history remains open.

Concept: scope-lifetime-finalization, R11.
Consumer: Atomic.Cleanup.log_debits.
Proof role: preservation.
Evidence status: proved.
Scope: actual shop source, all six request identities, arbitrary retained environments and native callback inputs.
The existing source fragment excludes layers, definitions, calls, raw generators, and captured acquisition-release constructors.
The actual shop discharges every restriction.
The statement adds no original scenario premise.

Base: 64fa52c0e.

Changed modules:
- src/Effect4/Laws/Program/NativeCallbacks.lean factors the existing select scope proof.
- Test/Dogfood/Scenario/Atomic/WriterSource.lean bounds actual compiled note producers.
- Test/Dogfood/Scenario/Atomic/WriterCallbacks.lean bounds value and cause callbacks.
- Test/Dogfood/Scenario/Atomic/WriterSuspensions.lean bounds actual suspended source branches and stored bodies.
- Test/Dogfood/Scenario/Atomic/WriterLoops.lean proves actual repeated bodies contain no selected note.
- Test/Dogfood/Scenario/Atomic/WriterFrames.lean consumes shared FrameWeights for success, failure, and interruption resume.

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic.WriterFrames` passes 1107 jobs.
The changed frame module takes 9.8 seconds.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AtomicWriterSourceAudit.lean` passes.
The audit reports 520 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.

Native finalizer issuance and actual note consumption use the separately checked WriterPhase laws.
Their complete machine command and history composition remains open.
The declarations add no second source carrier or execution carrier.
The source census uses kernel-checked equations over the actual symbolic program.
This proof contains no bounded execution or host evidence.
