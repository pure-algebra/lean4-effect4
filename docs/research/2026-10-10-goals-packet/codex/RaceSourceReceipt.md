# Race origins and worker reply sequencing

The actual Workers source excludes race cleanup, and every remaining native reply retains the saved callback sequence.
Whole-history release custody remains open.

## Placement

Concept: scope-lifetime-finalization, R11. Claim: `ReleaseCustody.Execution.history`, consumed by `Workers.Assertions.releases_step`.
`SourceScope.RaceAllowed` names an actual race action in the existing source address census.
The existing action, stored-program and runtime-race predicates carry this origin.
`RaceFreeSource.not_race` excludes that witness when the actual source has no race action.
Workers discharges this census for every job count and every successful build.
The original Workers statement and budgets stay unchanged.

`ReplySequencing.terminal` reads the existing `TerminalReply` and source predicates.
It proves saved-frame sequencing for success, failure and delayed cell reads.
Its race-cleanup case is impossible under the checked source restriction.
`ReplySequencing.no_races` also excludes native race commands through their actual lookup premise.
No new program representation, token table or machine carrier is introduced.
The unused unconditional `TerminalReply.code_at` helper is removed; producers retain their actual code proofs.
These helpers establish neither whole-history custody, source uniqueness nor progress.

## Landing

Base: `b5d5da24e`, which integrates the checked native action debit from `c8011af1`.
Changed modules: `NativeScope`, `NativeActionScope`, `NativeConfiguration`, `NativeEvaluation`, and `NativeCommands`.
`ReleaseCustody.ReplySequencing` joins the existing `Execution` endpoint.
`SourceFragment` discharges the extra internal premise for `Workers.Assertions`.
The law root reaches source-opportunity installation and the complete native action debit.
The existing heap and source-history proofs retain their shared carriers.

## Checks

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.NativeReplies Effect4.Laws.Program.ReleaseCustody.ReplySequencing Test.Dogfood.Scenario.Workers`.
Result: successful, 1131 jobs; `RaceSourceBuild.log` retains the output.
Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.NativeActionDebit Test.Dogfood.Scenario.SourceOpportunity Effect4.Laws`.
Result: successful, 1340 jobs; `RaceSourceIntegrationBuild.log` retains the output.
Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws Test.Dogfood.Scenario.Workers`.
Result: successful, 1339 jobs after the root imports join; `RaceSourceRootsBuild.log` retains the output.
Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/RaceSourceAudit.lean`.
The audit checks 1492 declarations within `[propext, Quot.sound]`, with no planned dependencies.
The status output retains `Execution.history` as its explicit remaining goal.
`RaceSourceAudit.out` retains both results.

## Remaining work

The native evaluator and complete command-history assembly remain on the path to the unchanged Workers release claim.
No runtime definition changes; the prior behavior receipt still describes those gates.
The final generated proof graph refresh remains due.
