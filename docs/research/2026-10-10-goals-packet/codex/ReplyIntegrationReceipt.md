# Native reply integration

The integrated reply producers and saved-frame extension compile without planned dependencies.
The original whole-history claims remain open.

## Placement

Concept: scope-lifetime-finalization, R11. Claim: `ReleaseCustody.Execution.history`, consumed by Workers cleanup.
`Sequencing.YieldPhase.refGet` admits the actual delayed cell-read reply beneath a saved forced yield.
`Sequencing.stable_refGet` retains the existing callback sequence after that reply installs.
This addition uses the actual stored-operation spelling and introduces no new execution carrier.
The native sequencing proofs retain all previous cases.

## Landing and checks

Base: `9ae06cda2`.
Changed files: `ReleaseCustody/Sequencing.lean` and `Test/All.lean`.
The test root now reaches the complete timeout park chain.
Agent commits `c86c7c5f`, `56c66763`, `4715d428`, `cfac990e`, and `b5bd41f4` are integrated.
The import conflict retains both checked dependency chains.

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Execution Test.Dogfood.Scenario.Routing Test.Dogfood.Scenario.SourceOpportunity Test.Dogfood.Proofs.HostTimeoutParkSteps Effect4.Laws`.
Result: successful, 1361 jobs; `ReplyIntegrationBuild.log` retains the output.
Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/ReplyIntegrationAudit.lean`.
The native reply, source-use and sequencing modules audit 1452 declarations with no planned dependencies.
The new timeout command and park modules audit 183 declarations with no planned dependencies.
All audited declarations remain within `[propext, Quot.sound]`.
`ReplyIntegrationAudit.out` retains both results.

## Remaining work

Race-cleanup replies require either their actual saved-stack relation or a discharged source exclusion.
Workers uses no race source; that exclusion belongs in the existing source predicate.
Whole-history release custody, source uniqueness and timeout result flow remain open.
The landing changes proofs only; the prior behavior-gate receipt remains applicable.
The final generated proof graph refresh remains due.
