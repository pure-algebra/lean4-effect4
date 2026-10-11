# Shared saved-frame scalar transport

The original source-history proof now consumes the shared scalar pop law.
The cleanup writer uses the same law with its active note projection.
Finalizer issuance and whole-machine writer transport remain separate obligations.

Base: `d0f636d05`.
Placement: scope-lifetime-finalization, R11, preservation steps of application registration and cleanup bounds.
Consumers: `SourceOpportunityFrames.getCont_le`, `Atomic.WriterPhase.pop_bound`, and their history transports.

`Machine.FrameWeights.Model` supplies current and saved scalar projections over existing primitive code.
Its premises retain the actual `ensure` stack bound and zero-weight replacement answers.
The proved census covers `answerOf`, `passPushed`, `popFrom` and `getCont`.
`SourceOpportunityFrames` instantiates that model with its existing source projections.
The change replaces the old pop census with applications of the shared law.
It adds no program syntax, execution state or scenario assumption.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.FrameWeights`: passes, 174 jobs; module compilation takes 1.3 seconds.
- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceOpportunity Test.Dogfood.Scenario.Atomic.Writer`: passes, 1092 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FrameWeightsAudit.lean`: passes.
- Audit: 188 declarations within `[propext, Quot.sound]`; zero planned goals and zero declarations modulo goals.

The checked existing application reader retains every job count and the original admitted-history carrier.
These scalar transport laws establish neither progress nor an outside-runtime observation.
The native finalizer start supplies writer permission outside the pure frame pop.
No behavior gate is owed for the proof-only extraction.
