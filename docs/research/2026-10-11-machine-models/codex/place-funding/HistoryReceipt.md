# Shared accounting history receipt

Both existing history consumers use one proof of the outer machine edits.
Their statements and source restrictions remain unchanged.

## Placement

Concept: scope-lifetime-finalization and reactive-scheduling, R11.
Question: existing finalizer custody and source-use claims need funding through actual histories.
Consumers: StackLedger.edits and SourceScope.Opportunities.budget_decision_lift.
Reach: native edits, distinct fiber identifiers, and zero race, command, and detached-task weights.
Clock updates and prepared replies retain explicit state-weight premises.
The interruption proof uses the actual event and update sequence in the shared edit alphabet.
These proofs establish no progress, source permission, or host observation.

## Changes and checks

The source base is 54d9ca79b718c2e3b3b2ac05293ba021983a41c4.
HistoryEvidence.json records every changed source hash.
HistoryHeaders.json records 29 unchanged named declaration statements against 914521577.
The four production files add 58 net lines, including the new shared 84-line module.
The saved-stack and source-use histories both consume the shared proof.

The combined build passes 1159 jobs, including both histories and Atomic.WriterMachine.
The two actual history readers pass with warnings treated as errors.
The nine-module audit passes 398 declarations within [propext, Quot.sound].
It reports zero planned goals and zero declarations modulo planned goals.
The combined build also checks the merged primitive accounting consumers.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.LedgerFinalizer Effect4.Laws.Program.SourceOpportunityHistory Test.Dogfood.Scenario.SourceOpportunity Test.Dogfood.Scenario.Atomic.WriterMachine
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/place-funding/HistoryReader.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/place-funding/HistoryAudit.lean
python3 docs/research/2026-10-11-machine-models/codex/place-funding/HistoryHeaders.py
```

HistoryBuild.log, HistoryReader.log, and HistoryAudit.log retain those results.
The source changes are LiftMachineFact, PlaceFunding.History, LedgerRun, and SourceOpportunityHistory under src/Effect4/Laws.
This slice changes proofs only, so no behavior gate runs.
The original application goals remain open.
