# Compatibility with the same-scope reference rule

The source view loses a refusal marker for one admitted layer-reference control.
The prepared view retains this existing display gap.
The finite control records it without changing production.

## Compatibility conclusion

The inspected sources at `3ef7aeb0` require no adaptation to the prepared view.
The prepared patch is integrated on the isolated branch at `e37402c3`; it is absent from primary by design.
Its run-view blob equals `ae80ada1`'s blob.

`Prepared built` still binds the original `built.program` and its exact `built.table`.
Controls still retain `s.built`.
The new `Eff.layerRefsWF` rule restricts references to the same lexical scope.
It restricts the programs accepted by `typeOfProgram` and retains the built input's structure and lifetime.
It introduces no source-address remapping.
A newly rebuilt program needs its own preparation, as before.

`compatibility-3ef7aeb0.json` records the frozen Git blobs inspected.
Of fourteen relevant source files, only `Program/Refs.lean` differs from the isolated base.
The other inputs include `Api.Built`, authoring admission, run controls, source annotation, the view and printed code.
No build or execution of `3ef7aeb0` runs.
The primary working tree has Claude's ongoing changes, which this comparison excludes.

## Retained finite control

`ReferenceViewControl.lean` runs at isolated commit `ae80ada1`.
The program supplies a numeric layer and references it at `[0, 1]`, targeting `[0, 0]`.
It has no definition body or host row.

- `Api.Author.Internal.finishBuild` accepts it.
- The source session's check refuses at `[0, 1]` with `layerReference` and has no root type.
- The prepared reference line has no type, note or refusal marker.
- The actual frame agrees with the former renderer and still prints a module.
- A reference-free control displays its root's numeric source type.

`reference-view-control.json` records the exact command, isolated head, source hash and passing exit code.
`reference-view-control.log` retains the displayed source lines.
The command uses `LEAN_NUM_THREADS=3`; only one narrow Lean invocation runs at a time.
These are finite controls, not generic annotation or view-agreement theorems.

## Why the marker is absent

`Api` admission checks well-formedness and the expansion through `typeOfProgram` in `src/Effect4/Program/Typing.lean`.
`prepare` opens an `EditSession` on the original source.
`Sketch.annotate` in `src/Effect4/Program/Typing/PartsTable.lean` checks that source.
`Checker.checkLayer` in `src/Effect4/Program/Checker.lean` refuses its raw reference.
`Annotate.atNode` in `src/Effect4/Program/Typing/Annotate.lean` records no result at a non-program sort.
The parent program entry carries the refusal at its child's path.
`Program.sessionPage` in `tools/Tools/View/Program.lean` marks only an entry whose refusal path equals its own path.
Neither entry supplies that combination, so the page loses the marker.

A future source-to-expansion connection must recover types and refusals at original source paths.
It must account for the checker's expansion, lexical typing context, row table, and fixed program.
Replacing the source with its expansion changes the address space and does not supply that connection.
The new same-scope rule proves no source-view annotation law.

## M7 evidence boundary

The commit message reports a passing narrow build, a cycle-aware audit and M7 with no planned goal.
The frozen source removes `crossScopeRef_builds` and replaces its use with same-scope typing.
The frozen plan battery requires `m7_proved` to have proved status.
The generated semantics file labels the M7 claims proved.
Those are independently inspected source records; this check does not rerun their build or audit.

`M7Fragment` in `src/Effect4/Laws/Program/Typed/Assembly.lean` requires a lawful checked source at an empty row table.
It also requires an empty requirement row and an answer-free tape.
M7 proof closure supplies no source-view annotation law, nonempty-table host agreement, performance bound or current source address for a fiber.
No production file, primary checkout, root import or authority document changes here.
