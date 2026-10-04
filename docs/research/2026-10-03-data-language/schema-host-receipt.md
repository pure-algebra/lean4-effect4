# Schema host comparison receipt

## Integration note

This slice adds finite host comparisons; it does not change the codec API or any theorem.
The fresh Lean emitter and pinned host comparison pass on integration commit `9f4e784c`.

Duplicate JSON keys remain a boundary difference.
Lean receives an entry list and refuses repeated names.
JavaScript text parsing produces an object and retains the last occurrence before Schema receives it.
The checker measures both results without calling them the same input.

For extra record fields, the matching refusal uses Effect's explicit `onExcessProperty: "error"` option.
The checker separately confirms that Effect's default decoder discards the extra field.
Neither behavior changes the Lean contract.

## Base and files

Branch: `codex/data-codec-host`, from `69ad9518`.
Source checkpoint: `0590aad5`, integrated as `9f4e784c`.

Only these files change:

- `harness/truth/schema-codec/Emit.lean`
- `harness/truth/schema-codec/check.ts`
- this receipt

The emitter retains all 17 inputs from `Test.Codegen.SchemaGenerationContract` and adds 15 local cases.
The shared test file remains unchanged.
All emitted results come from the public `Ty.encode` or `Ty.decode` operations.
No expected encoded value is copied into the emitter.

## Evidence and limits

The comparison belongs to Exact Codecs and Data Plane Embeddings and serves R2/R3.
It extends the finite target evidence beside the existing codec laws.
No theorem is added, repaired or weakened; no new axiom query is required.
It establishes no general agreement between Lean and Effect, target execution theorem or host liveness result.

The 32 encoding comparisons and host round trips cover the previous forms and the new data forms.
New cases include absent optional fields, present `Option.none`, present `Option.some`, and optional unit values.
Optional unit distinguishes absence from a present `undefined` host value, encoded as JSON null.
It does not add support for the separate `.undefined` type.

Records and string maps include empty, nonidentifier, Unicode, numeric-looking and `__proto__` names.
Object key order is outside the comparison; Lean retains its canonical UTF-8 order.
Controls check that prototype-sensitive names remain own properties.
Tuples cover arities zero through three and two nested combinations of records, maps, options and tuples.

Ten shared refusal cases cover missing and extra fields, incorrect value types and incorrect tuple lengths.
The two existing Result and Cause negative controls remain.
Three additional observations expose default extra-field handling and duplicate record or map keys after text parsing.
The checker refuses missing or unexamined fixture names.

## Commands and results

The source checkpoint passes the pinned target compiler:

```sh
harness/truth/node_modules/@typescript/native-preview/bin/tsgo --version
harness/truth/node_modules/@typescript/native-preview/bin/tsgo --project harness/truth/schema-codec/tsconfig.json
```

Version: `7.0.0-dev.20260629.1`.
The runtime comparison asserts Effect version `4.0.0-rc.112` before checking values.

The coordinator ran all three commands successfully against its checked dependencies:

```sh
LEAN_NUM_THREADS=3 lake env lean -M4096 --run harness/truth/schema-codec/Emit.lean /private/tmp/effect4-schema-host-values.ts
harness/truth/node_modules/@typescript/native-preview/bin/tsgo --project harness/truth/schema-codec/tsconfig.json
bun harness/truth/schema-codec/check.ts /private/tmp/effect4-schema-host-values.ts
```

The runtime reports 32 fresh comparisons, 32 host round trips, 10 matching refusals, two legacy negative controls and three explicit boundary differences.
No additional Lean build was needed.
Logs are `/private/tmp/effect4-schema-host-emit.log`, `/private/tmp/effect4-schema-host-tsgo.log` and `/private/tmp/effect4-schema-host-check.log`.
The seat read these logs before closing this receipt.

`git diff --check` and the focused controlled-English check pass.
No full sweep, dependency installation or push was run.
