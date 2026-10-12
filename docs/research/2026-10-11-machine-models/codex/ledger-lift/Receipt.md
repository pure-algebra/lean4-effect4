# Shared machine-fact attachment receipt

The source-budget decision proof now attaches its accounting to the existing source invariant.
All seven existing theorem statements remain unchanged.
The original cleanup goals remain open.

## Placement

Concept: scope-lifetime-finalization, R11.
Question: the original Workers and Atomic claims retain source-use accounting through actual decisions.
Role: helper of those existing registry claims.
Consumer: `Opportunities.budget_decision_lift` in `src/Effect4/Laws/Program/SourceOpportunityHistory.lean`.
The helper is `DecisionLift.withMachineFact` in `src/Effect4/Laws/Machine/LiftMachineFact.lean`.

The existing decision invariant supplies worlds, source ownership, command ownership, and drained-task ownership.
The attachment retains the same world transitions and every queue premise.
The machine fact supplies actual command preservation and the existing eight edit facts.
Its reply premise supplies the fact after actual preparation and the first resume.
No arbitrary reply or source permission follows from the attachment alone.
The theorem supplies neither progress nor outside-host agreement.

The source instance retains its fragment, sequential-source, race-free, clear-finalizer, and clear-loop premises.
It retains the fork ledger's distinct-owner invariant.
Its source and reply facts come from the existing producers.

## Change

Base: `d81746e9e0cafb6f0644426b007805a04fbdfd69`.
Head: the commit containing this receipt.
The two changed source paths are named above.
The source history imports the shared module, retaining library-root reachability.
No executable definition changes.

`Evidence.json` records the exact source hashes and all seven unchanged theorem headers.
The shared law has 74 lines.
The source history falls from 200 to 192 lines.
Its private thirteen-field decision construction falls from one to zero.
The total grows by 66 lines while moving the reusable construction to its shared owner.

## Verification

```sh
LEAN_NUM_THREADS=1 lake build Effect4.Laws.Machine.LiftMachineFact
LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.SourceOpportunityHistory Test.Dogfood.Scenario.SourceOpportunity Test.Dogfood.Scenario.Atomic.Cleanup
LEAN_NUM_THREADS=1 lake env lean /private/tmp/LedgerLiftAudit.lean
```

The shared build passes with 208 jobs.
The first consumer build reports a structure-field layout error.
The repaired consumer build passes with 1,132 jobs.
`FirstConsumerBuild.log` and `ConsumerBuild.log` retain both results.
The audit passes for 44 declarations within `[propext, Quot.sound]`.
It finds no planned goal or declaration resting on one in the two changed modules.
The Atomic application consumer still contains its original planned cleanup obligation.
Its successful build does not close that obligation.

The broader executable changes still owe their planned behavior sweep.
No behavior gate is reached by this proof-only slice.
