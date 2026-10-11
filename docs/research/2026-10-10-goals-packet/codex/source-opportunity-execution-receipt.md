# Source opportunity command settlement

Apply `control-weights-installation.patch` before importing the new execution module.
Its baseline is `ff35624f:src/Effect4/Laws/Machine/ControlWeights.lean`.
The patch adds only `ControlWeights.replace_sum_le_omitted` to that existing module.

- Proof role: preservation.
- Evidence status: proved.
- Concept: scope-lifetime-finalization, R11.
- Consumer: application registration bounds and `Workers.Assertions.registrations_step`.
- Base: `f94f3708`.
- Shared base dependency: Moves and Footprint from `7c69f880`.

## Changes

The generic installation bound consumes `ControlWeights.replace_sum` and `ControlWeights.omit_sum`.
It requires distinct keys but permits the selected owner to be absent.
Settlement consumes the bound across every scheduler outcome.

The actual native iteration includes deferred interruption, operation charging, and forced yield.
The actual loop and deliver commands compose that debit with settlement.
They consume `Moves.iteration_id` and `Moves.evaluateNative_footprint` for identity.
They consume the existing ForkLedger invariant for distinct stored identities.

The Workers reader applies the loop command to full admitted histories.
It retains every job count and both source acquisition sites.
It discharges source restrictions from the unchanged built program.

## Checks

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceOpportunity` succeeds with 1087 targets.
Execution takes 1.4 seconds; its scenario reader takes 2.9 seconds.

`LEAN_NUM_THREADS=3 lake env lean /private/tmp/SourceExecutionAudit.lean` succeeds.
The audit checks 67 declarations within `[propext, Quot.sound]`.
It reports zero planned goals and zero declarations modulo planned goals.

## Open work

The remaining non-evaluator commands and decision edits still need debit composition.
No whole-history source-use bound or final registration bound is claimed here.
