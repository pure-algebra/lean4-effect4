# Record source and runtime receipt

The TypeScript record helpers and both printed-source walks agree on the tested record forms.
This evidence is finite. The Lean structural reconstruction theorems remain the proof boundary.

Base: `d922631c`. Branch: `codex/data-language-wave`.
The commit containing this receipt records the source changes and generated outputs.

## Changes

`tools/Drivers/TsGen.lean` derives metadata descriptors, wire tags, frame tags, subtype edges, variance and identifier data from their existing owners.
It produces `ts/eff/test/type-projection.gen.json` by evaluating the core normalization, metadata and target type functions.
The Makefile declares the fixture, variance input and runtime helper inputs for the affected checks.

`ts/eff/metadata.ts` reads the generated canonical type metadata without normalizing the stored declaration.
It refuses malformed frames, noncanonical digits, unpaired surrogates and natural numbers outside JavaScript's exact integer range.
The Lean structural metadata theorem keeps its unrestricted natural domain.

`ts/eff/target-types.ts` compares the retained metadata with its target annotation.
Its policy tables come from the existing Lean owners.
Its type cases refuse or require a source update when the generated type language grows.
The comparison has finite cross-language evidence, not a general simulation theorem.

`ts/eff/read.ts` and `ts/eff/ingest/ck.ts` recognize construction, both read modes and overwrite through their separate source walks.
They share the metadata decoder and annotation comparison.
The strict foreign-source profile stays separate from the printed-source entry points.
The source reader refuses changed annotations, key forms, argument counts and overwrite order.

`harness/truth/records.ts` implements the three executable helpers.
Optional reading tests own-property presence, so present undefined and nested empty options remain present values.
Overwrite uses the printed object spread and evaluates target before replacement.
Computed prototype keys create own properties without changing the prototype.
The raw fallback has no executable helper. Checked production refuses unsupported stored annotations before it can emit that fallback.

Both truth lanes use `copy_prelude` in `scripts/lib/truth_host.py` to stage the runtime helper beside the prelude.
The truth producer updates the generated modules through its existing emission command.
Every changed module differs only in the added helper imports.

## Proof placement and limits

Concept: Exact Codecs and Data Plane Embeddings. Claim served: `printed-modules`. Requirements: R2 and R3.
Role: source implementation and finite controls for exact record metadata and structural reconstruction.
The source controls retain raw declared fields, supplied names, read modes and overwrite keys.
They add no theorem about arbitrary source parsing or TypeScript assignment.

Concept: Observation and Simulation. Claim served: `run-eq-meaning`.
Role: finite host controls for the named record fragment.
The runtime checks compare explicit presence, field values, property names and evaluation order.
They add no general target execution, scheduling, host-session or liveness theorem.

## Verification

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 python3 scripts/generate.py --only ts` | Passed. The driver build reports 111 jobs. |
| Repeated TypeScript generation with SHA-256 comparisons | All nine generated files retain identical bytes. |
| `ts/eff/node_modules/.bin/tsgo --version` | `7.0.0-dev.20260629.1`. |
| `ts/eff/node_modules/.bin/tsgo --noEmit -p ts/eff/tsconfig.json` | Passed. |
| `ts/eff/node_modules/.bin/tsgo --noEmit -p harness/truth/tsconfig.json` | Passed, including the regenerated modules and record type controls. |
| `bun test ts/eff/test harness/truth/records.test.ts` | Passed 379 tests, with 1487 assertions. |
| `bun test ts/eff/ingest/test` | Passed 272 tests, with 1526 assertions. |
| Truth producer `--emit` against the committed corpus in an isolated directory | Passed. All 37 generated modules differ only in helper imports. |
| Isolated `copy_prelude` check | All three files match their sources byte for byte. |

Independent source review found four missing primitive type spellings in the direct reader.
The repair adds `any`, `object`, `symbol` and `bigint`, with both-reader controls for absent optional fields.
The repeated checks above include the repair.

No full proof battery or full truth execution runs in this slice.
The shared Lean compiler slot stays serialized across the implementation seats.
