# Integrated native command checkpoints

The combined build and audit pass. The original history obligations remain open.

Base: `1f1a16dc9`. Agent checkpoint head: `d55c6db25`.

The five checkpoints add native source debit, cancellation ownership, saved-frame settlement, charged iteration debit, and timeout command custody.
The library root reaches the primitive source theorem through `SourceOpportunityPrimitive`.
The custody execution module reaches both command sequencing and iteration debit.
The battery root reaches the timeout driver.

Validation:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws Test.Dogfood.Scenario.SourceOpportunity Test.Dogfood.Scenario.Workers Test.Dogfood.Proofs.HostTimeoutDriver`: passes, 1388 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/CheckpointIntegrationAudit.lean`: passes.
- The audit checks 1665 declarations within `[propext, Quot.sound]`; none rests on a planned goal.

The audit establishes proof trust for the listed modules. It establishes no whole-history endpoint or outside implementation agreement.
Behavior gates remain scheduled after the major proof structures land.
