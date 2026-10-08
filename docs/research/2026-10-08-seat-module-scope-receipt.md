# Module step scope receipt

`Step.scoped` checks every current constructor, including folds, records, deferred comparisons, and flat triples.

The base is `71c451b5`, including the shared step laws and the tuple constructor checkpoint.
The changed source is `src/Effect4/Laws/Modules/Step/Scope.lean`.

## Placement

Concept: `initial-algebras-folds`.
Requirement: R4.
Role: helper of `operation-data-scoped`.
Consumers: module operation scope laws and `Api.Author.build`.

`Step.scopedAt` retains caller input scope at one environment and path.
A fold freezes outer source resolution at that environment.
`weaken_scoped` inserts each binder slot and retains the term scope judgment.
`Step.scoped` lifts the local statement to the authoring scope judgment.
`Input.source_scoped` supplies its premise from the caller's scoped source list.

Scope proves neither typing nor progress.
No statement crosses the host boundary.

## Checks

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Step.Scope` passes with 374 jobs.
`LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-scope-check.lean` checks a concrete fold reader and an out-of-scope input control.
The scratch audit reports `[propext, Quot.sound]` for `Step.scopedAt`, `Step.scoped`, and `weaken_scoped`.
The root imports and full battery remain coordinator work.
