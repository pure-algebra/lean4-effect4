# HO-3a generated TypeScript follow-up

The existing packet at `648fe735` supplies the design findings and their five-point placement.
This follow-up tests actual output of the working HO-3a TypeScript printer.
The owner base remains `41151468ffd97d0df25ed7d13080eee783ab199e`.

## Completion criteria

Generate the modules from accepted Lean programs using the owner's compiled imports.
Keep each generated declaration unchanged when adding its explicit external imports and fixtures.
Check negative and positive twins with pinned tsgo 7.
Audit the newly connected module reconstruction laws.
Record source hashes before and after every run.
Persist the results and the updated review checkpoint locally.

## Placement

1. Concepts: `exact-codecs` for module reconstruction and `translation-simulation` for target observations.
2. Question: `module-defs-round-trip`, role `compatibility`, pointer `readModule_printModule_defs` in `src/Effect4/Laws/Codegen/Module.lean`.
   Consumers are `ModuleEmission.readModule` and `Api.printModule_roundTrip` in `src/Effect4/Laws/Api/ModuleReadable.lean`.
   The target controls serve R8 separately from that structural theorem.
3. Reach: unused parameter-bearing definitions and service declarations, so no program requires HO-3b invocation printing.
   Payload names, external row roots, trailing identifiers, and service forwarding are the target boundaries under test.
   Parameter-only payload types test whether the shared annotation inventory supplies every printed class.
   Decisions rows 340 and 341 retain their slice order.
4. Limits: finite target rejection establishes no universal simulation or source typing defect.
   A reconstruction theorem need not guarantee target lexical binding or target acceptance.
   Compiled imports are reused; this follow-up does not rebuild the owner's worktree.
5. Requirement: R8, the generated program's connection to its source.
   Service forwarding supports R5 later; HO-5 remains deferred.

No new theorem or planned goal is introduced.
The law audit checks the existing paired-body reconstruction route and its dependencies.

The annotation inventory probe serves module emission under R8.
Its consumer is `ClassTable.moduleClasses` in `src/Effect4/Codegen/ClassTable.lean`.
It compares a type mentioned only by a callback with that type mentioned by an ordinary definition column.
It establishes no general formation theorem and introduces no new obligation.

## Raw formation control placement

1. Concept: `subtyping-algebra`, required property `raw-formation` in `docs/core/semantics.md`.
2. Question: `raw-formation`; its existing pointer is `Formation.checkInput_eq_none_iff` in `src/Effect4/Program/Formation.lean`.
   The control tests the inventory that supplies this judgment, rather than changing the theorem.
   `ArgAll` and `declAnnotations_all` in `src/Effect4/Laws/Program/Typing/Closed.lean` describe the same inventory.
3. Reach: an unused callback whose request repeats a record field, compared with an ordinary declaration request.
   Decisions rows 192, 193, and 340 bound this raw input check.
4. Limits: finite raw acceptance does not refute output closedness or prove a runtime type violation.
   Closedness and raw record formation remain distinct judgments.
5. Requirement: R14 for raw type formation; R8 for the shared target inventory.

The control introduces no theorem or planned goal.
