# Shared frame weights integration

The source-history and Workers consumers pass on the goal branch.
The original cleanup write obligation remains open.

Base: `19a484c02`.
Integrated source commit: `9ac218a70`, landed as `e57a9cd7a`.

Placement: scope-lifetime-finalization, R11.
Question: shared saved-frame transport serves source registration and Atomic cleanup write bounds.
Reach: the existing primitive frame and explicit scalar-model premises.
Limit: this extraction establishes no whole-history cleanup writer or progress property.
Consumer: `SourceOpportunityFrames.getCont_le` and the Atomic writer phase.

Commands:

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceOpportunity Test.Dogfood.Scenario.Workers Test.Dogfood.Scenario.Atomic.Writer`: passes, 1171 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FrameWeightsAudit.lean`: passes.
- Audit: 188 declarations within `[propext, Quot.sound]`; zero modulo planned goals; zero planned goals.

The retained logs contain the measured results.
This proof extraction changes no runtime behavior or target output.
The earlier behavior sweep retains its documented observation limits.
