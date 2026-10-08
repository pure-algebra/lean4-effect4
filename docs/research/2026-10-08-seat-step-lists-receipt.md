# Shared list authoring checkpoint

The list bodies read the current item and the outer inputs alone.
The builders insert a private accumulator through typed input renaming.
The output remains the existing first-order Step data.

Base checkpoint: 722d72ea, with renaming in fca76c16.
Changed files: Modules.Step.Lists and Laws.Modules.Step.Lists.
The authoring renaming function is not stored syntax.
MapWith takes an output list witness only to choose its empty-list type.
Same-type map needs no extra witness.

Placement: Translation Simulation, helper of step-language-sound, requirement R10.
The input-renaming reading serves the list equations and named binder authoring.
The list equations serve Pool, Semaphore, and Queue operation agreement statements.
Each equation applies at every interpretation and input carrier.
Map computes List.map; filter computes List.filter; removeBy negates its predicate; any computes List.any.
These statements establish no typing, membership, allocation, progress, or host execution claim.
Shared Step reading and typing remain the source-term boundary.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Modules.Step.Lists Effect4.Laws.Modules.Step.Rename`: core modules passed; the first renaming proof attempt required constructor repairs.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Step.Rename`: passed after those repairs.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Step.Lists`: passed after explicit carrier annotations.
- `LEAN_NUM_THREADS=3 lake env lean /private/tmp/step-lists-control.lean`: passed.

The finite control checks map, filter, removal, both any outcomes, an empty map, and normal forms.
The trust control audits the four shared modules through auditedFacts and reachedAxiomsMany.
It checks 34 declarations and permits only propext and Quot.sound.
No declaration rests on `sorryAx`.

HeadOr waits for the coordinator's getOrElse constructor checkpoint.
Module pass migration follows the named authoring binder checkpoint.
Roots and registers remain coordinator-owned.
