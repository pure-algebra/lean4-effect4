# Tuple target receipt

## Integration note

Add `Test.Codegen.Tuple` to the battery root.
The core modules are reached through `PrintLeaf`; the proof modules are reached through `ReadLeaf`.
The coordinator owns the root imports, generated inventories and aggregate policy case checks.

The Lean structural boundary retains every natural index.
The JavaScript reifier refuses indices above `Number.MAX_SAFE_INTEGER`, because its stored index is a JavaScript number.
This cut does not add a premise to `readTerm_printTerm`.

## Base and commits

The branch is `codex/tuple-codegen`, created from integration checkpoint `b1f5b9e0`.
The previous record branch remains intact.

- `995a418a`: checked tuple target source and the shared natural-text decoder.
- `70122ca3`: checked target helper, both source readers and target fixtures.
- `09939e9e`: checked structural laws and Lean fixture; the final implementation head.
- Coordinator companions: `0b357b3e` and `c101f5cf`, applied here as `ba089552` and `eceb7827`.

## Changes

`Data/NatDecimal.lean` owns the existing byte-decimal fold.
`Program.digitOfByte` and `Program.decodeBytes` remain aliases.
The existing public decimal theorem names remain available through `ReadLeaf`.
Their proofs now live in `Laws/Data/NatDecimal.lean`.
The clock carrier is unchanged.

`Codegen/Tuple.lean` writes `tupleAt<"2">("2")(target)` and reads only matching canonical decimal markers.
`PrintLeaf` and `Read` connect that wrapper to `Term.tupleAt`.
`Program.termHelperNames` excludes record and tuple helper names from row and export names.
`Codegen.Diagnostics.codesOf` covers tuple terms and tuple refusals without inventing a measured target diagnostic mapping.

The target helper in `harness/truth/tuples.ts` uses a readonly tuple key constraint and introduces no assertion.
It retains literal results, union results and `never`.
Both target source readers validate the marker shape and the exact numeric storage boundary.
`harness/truth/tsconfig.json` includes the new tuple type fixture.
Existing record behavior stays covered by the focused regression run.

The affected proof files are `Laws/Codegen/ReadLeaf.lean`, `Laws/Codegen/Tuple.lean` and `Laws/Data/NatDecimal.lean`.
The new Lean fixture is `Test/Codegen/Tuple.lean`.
Target fixtures are `tuples.test.ts`, `tuples.typecheck.ts` and `ts/eff/test/tuple-syntax.test.ts`.
The target source files are `ts/eff/read.ts`, `ts/eff/ingest/ck.ts`, `ts/eff/tuple-index.ts`, and the truth prelude.

## Theorem placement

Concept: Exact Codecs and Data Plane Embeddings.
Claims: helpers of `collection-term-print-read` and `printed-modules`; requirements R2 and R3.
The byte-decimal retraction feeds `Tuple.readAt_writeAt`; decimal exactness feeds `Tuple.readAt_exact`.
The existing variable-name and service-key facts consume the shared decoder too.

Wrapper retraction quantifies over every natural index and arbitrary child expression.
Wrapper exactness assumes only successful structural reading.
`Tuple.readAt_size` supplies the recursive reader's termination bound under that same success premise.
The public term retraction retains scope as its only premise; the exactness statement retains successful reading as its premise.
The checked direct consumers include `Read`, `ReadPrint` and `PrintReadable` in the Laws graph.

These facts establish structural reconstruction, not rendered-source recognition, target execution, host cooperation or liveness.
The target tests supply finite evidence at their stated compiler and runtime.
No new program or type representation is introduced.

## Commands and results

The source checkpoint passes with 99 jobs:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Codegen.Tuple Effect4.Codegen.Read Effect4.Codegen.Diagnostics
```

The final structural checkpoint passes with 278 jobs:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Codegen.Tuple Effect4.Laws.Codegen.ReadLeaf Effect4.Laws.Codegen.PrintReadable Test.Codegen.Tuple
```

The fixture reports ten axiom queries.
Every query uses only `[propext, Quot.sound]` or a subset; decimal exactness uses no axioms.
The queries include both public term reconstruction laws and the existing key and variable-name facts.

Both target projects pass with pinned tsgo `7.0.0-dev.20260629.1`:

```sh
ts/eff/node_modules/.bin/tsgo --version
ts/eff/node_modules/.bin/tsgo --noEmit -p ts/eff/tsconfig.json
ts/eff/node_modules/.bin/tsgo --noEmit -p harness/truth/tsconfig.json
```

The focused run passes 383 tests with 1460 assertions across seven files:

```sh
bun test harness/truth/tuples.test.ts harness/truth/records.test.ts ts/eff/test/tuple-syntax.test.ts ts/eff/test/data-records.test.ts ts/eff/test/record-syntax.test.ts ts/eff/test/record-tags.test.ts ts/eff/test/read.test.ts
```

Controls cover empty, singleton, pair and larger tuples, exact literal types, unions, nested access, impossible receivers and one receiver evaluation.
They refuse absent positions, ordinary arrays, non-tuples, mismatched markers, noncanonical decimals and number rounding.
The Lean fixture retains an exact rendered index above the JavaScript number bound.

`git diff --check` passes.
The brief and receipt pass their focused controlled-English check.
No full sweep or push was run.
