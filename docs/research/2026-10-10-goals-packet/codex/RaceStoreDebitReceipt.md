# Native race and store command funding

The race and store command bounds compile; whole-history custody remains open.
The integrated source-opportunity and selected-owner proofs also pass their independent audits.

## Placement

Concept: scope-lifetime-finalization, R11.
Claim: `ReleaseCustody.Execution.history`, consumed by `Workers.Assertions.releases_step`.
Race launch transfers one pending program's credit into its actual spawned child.
Registration completion and exit callbacks introduce only administrative continuation code.
Scope linking and task posting retain or discard existing foreign release credit.
The due drain converts native completions into zero-credit resumes.
These local proofs establish no source uniqueness, whole-history custody or progress.

## Landing

Base: `34a53483e`.
Files: `CommandRaceDebit.lean`, `CommandStoreDebit.lean`, their Execution import, the actual command reader, and proof roots.
The roots also join the independently checked `SourceOpportunityFrames`, `NativeStacks` and `IterationDebit` modules.
No runtime definition changes.

## Checks

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution Test.Program.CommandDebit Test.Dogfood.Scenario.SourceOpportunity Test.Dogfood.Scenario.Workers Effect4.Laws`.
Result: success, 1334 jobs; `SourceOpportunityIntegrationBuild.log` retains the first combined build.

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution Test.Program.CommandDebit Test.Dogfood.Scenario.Workers Effect4.Laws`.
Result: success, 1326 jobs after store command integration; `RaceStoreDebitBuild.log` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/RaceStoreDebitAudit.lean`.
Result: 56 declarations within `[propext, Quot.sound]`, no planned dependencies; `RaceStoreDebitAudit.out` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineOutside.lean`.
Result: 196 declarations within `[propext, Quot.sound]`, no planned dependencies; `MachineOutsideIntegration.out` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/SourceOpportunityAudit.lean`.
Result: 599 declarations within `[propext, Quot.sound]`, no planned dependencies; `SourceOpportunityIntegration.out` retains the output.

## Remaining work

Countdown observers and evaluator assembly still feed whole-history custody.
Whole-history source uniqueness also remains open.
The original application statements remain unchanged.
Behavior gates retain the previous receipt's scope because this landing changes only proofs.
The final generated proof graph refresh remains due.
