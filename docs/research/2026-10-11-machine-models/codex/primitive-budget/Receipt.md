# Source-budget producer receipt

The existing source-budget proof consumes the shared primitive producer.
Its fifteen theorem statements remain unchanged.
This slice proves no remaining application goal.

## Placement

Concept: scope-lifetime-finalization, R11.
Question: source-use accounting for `Workers.releases_once` and `Atomic.cleans_once`.
Role: helper of those existing registry claims.
The changed helper is `Opportunities.primitive_debit` in `src/Effect4/Laws/Program/SourceOpportunityPrimitive.lean`.
Its consumers are the existing native, command, and source-opportunity history proofs.

The proof retains lexical ownership, sequential source, race-free, clear-finalizer, clear-loop, and distinct-owner premises.
It retains the actual registration, lookup, countdown, and current-code equations.
It adds no admission rule, progress claim, or source permission.
The host boundary stays unchanged.

## Change

Base: `5c0c4eab333a4fb605bca27fda1eccad5ca9fe31`.
Head: the commit containing this receipt.
Source: `src/Effect4/Laws/Program/SourceOpportunityPrimitive.lean`.
Evidence: this directory's plan, commands, audit, and measured source record.

`Moves.evaluatePrim_producer` supplies the actual evaluator branch.
The proof no longer classifies `evaluatePrim` itself.
It handles the producer's fourteen branches explicitly.

`Evidence.json` records fifteen unchanged theorem headers.
The source grows from 267 to 279 lines.
Its private evaluator splits fall from one to zero.

## Verification

```sh
LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.SourceOpportunityPrimitive Effect4.Laws.Program.SourceOpportunityHistory
LEAN_NUM_THREADS=1 lake env lean /private/tmp/SourceBudgetProducerAudit.lean
```

The build passes with 558 jobs; `Build.log` retains the output.
The audit passes; `Audit.log` retains the output.
It checks 139 declarations within `[propext, Quot.sound]`.
It finds no planned goal or declaration resting on one.
`Audit.lean` retains the audit command.

No executable definition changes, so this slice reaches no behavior gate.
The broader machine and target changes still owe their planned sweep.
The original application goals remain open as recorded in the integration plan.
