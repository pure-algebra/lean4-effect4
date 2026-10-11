# Actual frame-weight resume integration

The scalar bounds consume actual value and cause resume operations; they do not establish scenario writer history.

Base: `42bab7d97`.
Integrated source: `64fa52c0e`, landed as `34165e835`.

Concept: scope-lifetime-finalization, R11.
Consumers: Atomic cleanup writer counts and source-opportunity frame accounting.

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.FrameWeights Test.Dogfood.Scenario.SourceOpportunity`.
Result: passed, 1094 jobs.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FrameWeightsResumeIntegrationAudit.lean`.
Result: 258 declarations within `[propext, Quot.sound]`, no planned goals, and no declarations modulo goals.

The build log and audit output are retained beside this receipt.
This proof-only integration reaches no behaviour gate.
The original Atomic log-history obligation remains open.
