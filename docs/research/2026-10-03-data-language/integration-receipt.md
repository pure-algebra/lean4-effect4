# Data-language integration receipt

## Integration note

The data-language implementation is checked on `codex/data-language-wave`.
The branch starts at `82d34358`, verified against the remote branch before development.
The commit containing this receipt supplies the resulting head.
The primary checkout remains unchanged. No push or merge runs.

Records, string maps and fixed tuples now pass through authoring, checking, execution, TypeScript printing, Schema conversion and JSON codecs.
The host-session correspondence and OCaml lowering proofs remain separate work.
The [host-instance note](host-instance-follow-on.md) identifies the next representation dependency.

## Changes and ownership

The [plan](plan.md) records the dependency order.
The generator bootstrap precedes new constructors.
Raw formation and instantiated row formation precede value operations.
Each source receipt records its changed files, proof placement and focused checks.

| Surface | Source evidence |
| --- | --- |
| Raw formation and row instances | [Admission receipt](admission-receipt.md) |
| Record construction and reads | [Record integration](record-integration-receipt.md) |
| Record overwrite and tag selection | [Overwrite receipt](record-set-receipt.md), [tag receipt](record-tag-receipt.md), [printer ruling](record-elimination-ruling.md) |
| String maps | [Map proofs](map-proof-receipt.md), [handle containment](map-handles-receipt.md), [target checks](map-target-receipt.md) |
| Fixed tuples | [Checker receipt](tuple-checker-receipt.md), [world membership](tuple-world-receipt.md), [target reconstruction](tuple-target-receipt.md) |
| Schema and JSON | [Schema receipt](schema-data-receipt.md), [JSON receipt](json-codec-receipt.md) |
| Effect Schema comparisons | [Host receipt](schema-host-receipt.md) |
| OCaml conversions | [OCaml receipt](tuple-ocaml-receipt.md) |

`Effect4.Api` exposes tuple authoring beside records and maps.
`Test.Api.TupleAuthoring` constructs, binds, selects, checks, prints and executes a three-item tuple through that public import.
Its negative control refuses an absent position.
The law root and battery root include the new modules at their existing anchors.
The truth prelude inventory includes empty and positional tuple controls.

Touched documentation follows the existing vocabulary.
The project entry point links this receipt and the next host-session dependency.
The semantics authority states required properties; the generated report owns their measured proof status.
No second proof graph or program representation is introduced.

## Proof placement

The source receipts retain the five required placement fields for each new obligation.
`collection-term-print-read` registers the existing `readTerm_printTerm` statement, with scope as its only premise.
Its term fragment includes every natural tuple index and raw record declarations.
`record-codec-layout` points to `Schema.decode_iff`, whose observation is JSON equality under `normJ`.
These compatibility claims belong to Exact Codecs and serve R2 and R3.
Their printed statements appear in `generated/semantics.md` within the configured semantic axiom ceiling.
They establish no target execution, host cooperation, progress or liveness theorem.

`Ty.ofSchema` retains raw record property order and duplicates.
It performs conversion without certifying formation.
The normalizing writer is `Ty.schema`; the reader does not normalize before admission.
A bounded source review finds no production path that silently certifies malformed raw declarations through that conversion.

## Final integration checks

All commands run from the development worktree unless a linked receipt names another location.

| Command or check | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Test.Api.TupleAuthoring` | Passed; 131 jobs |
| `LEAN_NUM_THREADS=3 lake build Effect4 Conform Effect4.Laws.Program.Typing.Check` | Passed; 410 jobs |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws Test.Program.TypedProgBindRed Test.Program.ProtocolPosts semantics-report` | Passed; 638 jobs |
| `LEAN_NUM_THREADS=3 make check-cases` | Passed; 211 measured case sites, no refused or unresolved row |
| `bun test harness/truth/prelude-inventory.test.ts harness/truth/tuples.test.ts harness/truth/maps.test.ts` | Passed; nine tests and 127 assertions |
| `ts/eff/node_modules/.bin/tsgo --noEmit -p harness/truth` | Passed under pinned tsgo `7.0.0-dev.20260629.1` |
| `python3 scripts/generate.py --only readme` and `bun ts/eff/ingest/render-readme.ts --check` | Passed |
| `LEAN_NUM_THREADS=3 lake exe semantics-report /private/tmp/effect4-data-semantics` and a second output directory | Passed; JSON and Markdown outputs match byte-for-byte |
| `LEAN_NUM_THREADS=3 lake env lean -M4096 --run tools/Tools/RowTypes.lean generated/row-types.tsv` followed by `--check` | Passed |
| `bun tools/target/rows.ts --repo . --promote` followed by the same command without `--promote` | Passed; the promoted report matches the second observation |

The Schema host check runs these commands:

```sh
LEAN_NUM_THREADS=3 lake env lean -M4096 --run harness/truth/schema-codec/Emit.lean /private/tmp/effect4-schema-host-values.ts
harness/truth/node_modules/@typescript/native-preview/bin/tsgo --project harness/truth/schema-codec/tsconfig.json
bun harness/truth/schema-codec/check.ts /private/tmp/effect4-schema-host-values.ts
```

They pass with 32 fresh encoding comparisons, 32 host reconstructions, ten matching refusals and two retained negative controls.
Three explicit boundary differences remain recorded.
Strict host decoding requires `onExcessProperty: "error"` to refuse extra record fields.
Default host decoding discards them; host JSON text parsing collapses duplicate keys before Schema sees the object.
These controls cover optional presence, computed keys, empty maps, nested data and exact tuple lengths.
They establish finite observations against Effect rc.112, not a universal simulation.

The constructor policy retains its authored notes and adds only measured changes from this slice.
Direct Schema and codec case sites disappear because their definitions now use exhaustive generated folds.
The new tag and tuple default arms explicitly refuse unsupported shapes.
The report initially refuses three counterexample rows using an unsupported status word.
Those repaired counterexamples now use the register's existing `REPAIRED` status.

The target row report queries 22 operation rows and 40 atoms.
All six map signatures agree at the report's explicit type arguments.
The tuple constructor remains refused by the generic-signature report, which cannot instantiate its custom variadic scheme.
Concrete tuple type and execution controls remain the evidence for that target surface.
The report retains its prior mismatches and refusals; regeneration claims no additional agreement.

The `lcnf`, `eff`, `wire` and `cas` producers run in that order.
Their repeated outputs match byte-for-byte, including the generated OCaml engines and new constructor goldens.
The OCaml receipt records the pinned build, 555 golden checks, 6,330 wire checks and 107 engine checks.
The focused tuple target receipt records both pinned compiler checks and 383 tests with 1,460 assertions.
These are finite checks and do not establish a universal target simulation.

## Boundaries

The Lean structural tuple reader retains every natural index.
The JavaScript source reader refuses indices outside its exact numeric carrier.
OCaml controls cover indices within its measured 63-bit integer carrier.
No broader numeric representation claim follows.

JSON exactness uses the existing `normJ`, which retains duplicate object keys.
The JSON text parser and target helper implementations remain host boundaries.
The new codec shapes add no unsupported leaf codec.

The host-session follow-on needs checked call-site type metadata before proving correspondence to the waiting continuation.
An empty runtime list cannot identify its static element type.
The note proposes that metadata boundary without storing functions or introducing another program IR.

The whitespace check excludes only `generated/row-types.tsv`, whose final tabs retain required empty columns.
A separate check confirms eight columns and no trailing spaces in that file.

No whole battery, whole-library axiom gate or full sweep runs.
Focused theorem queries and the semantic report retain the configured trust ceiling.
The open M5–M7 and lowering obligations retain their existing statements and status owners.
