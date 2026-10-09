# Tuple context review

The distinct generic-arity overload is a checked finite alternative.
It still needs a checked TypeScript module printer and named erasure connection before production use.
A global distributed return regresses existing contextual inference.
A disconnected default return parameter accepts false result types.

## Placement and scope

- Proof role: none; this research packet states no Lean theorem.
- Evidence status: finite strict compiler controls.
- Scope: tuple product output and existing `Ref.modify` inference.
- Base: `7eb45da5` on `codex/synchronized-ref-pure`.
- Existing helper source: `bcf8a2514b6eb5efc5742297c6fbcf2172fd4ba4`.

The retained `controls.ts` evaluates seven candidate signatures and the helper-free callback result.
The retained `control-counterexamples.ts` pins the two smallest counterexamples and the checked alternatives.
`evidence.json` records the compiler, package, inputs, diagnostic count, and exit statuses.
`diagnostics.txt` retains the failed compiler output.
`positive-diagnostics.txt` is empty.

## Checked findings

The compiler is tsgo `7.0.0-dev.20260629.1`.
The package is Effect `4.0.1`.
Both use the existing release install; no package installation runs.

`fixedProduct` has the correct union of two readonly tuples before a helper participates.
`Ref.modify(cell, state => fixedProduct)` still refuses because contextual inference selects `None<number>` for the answer.
Explicit `Ref.modify<number, Option.Option<number>>` accepts that same value.
An explicit callback return `readonly [Option.Option<number>, number]` also accepts it.
Both alternatives retain the full Option answer type.
This is a compiler inference boundary, not evidence that the value has the wrong type.

The defaulted return alias appears to accept both tuple product output and the modify callback.
It also accepts `readonly [string, boolean]` as the result of numeric inputs.
The apparently accepted modify result has answer type `unknown`.
The positive control refuses to assign that result to `Effect.Effect<Option.Option<number>>`.
The alias is therefore a rejected candidate.

The original fold, select, tuple, and literal type controls pass with their expected refusals.
Their inputs remain byte-identical to the named source commit.
The temporary pure prelude reexports atoms, records, tuples, and control helpers.
The check uses the unchanged packet compiler options.

The compiler commands are:

```sh
node /Users/pooks/Dev/lean4-effect4/ts/release/node_modules/@typescript/native-preview/bin/tsgo --pretty false --noEmit -p /private/tmp/effect4-tuple-alternative-review/tsconfig.json
node /Users/pooks/Dev/lean4-effect4/ts/release/node_modules/@typescript/native-preview/bin/tsgo --pretty false --noEmit -p /private/tmp/effect4-tuple-alternative-review/positive.tsconfig.json
node /Users/pooks/Dev/lean4-effect4/ts/release/node_modules/@typescript/native-preview/bin/tsgo --pretty false --noEmit -p /tmp/stream-tuple-selective-probe/tsconfig.json
```

The first command fails as retained in `diagnostics.txt`.
The second command passes the counterexamples and original controls.
The third command independently passes the scout's distinct generic-arity overload controls.

## Smallest coherent connection

The scout keeps the ordinary tuple overload first, with one generic argument.
The second overload takes two generic arguments and returns the checked Cartesian product.
The checked printer chooses the second overload by supplying both actual slot types.
The pair overload uses the opposite generic arities because its existing signature already takes two types.
The probe accepts ordinary Option-valued modify callbacks and explicit product output.
It refuses wrong payloads and extra runtime tuple arguments.
This evidence establishes no general target typing theorem.

`Codegen.ModuleEmission.generated` in `src/Effect4/Codegen/Checked.lean` indexes `Program.printEntry`.
`Program.printModule` and `Program.printDef` in `src/Effect4/Codegen/Print.lean` call the ordinary expression printer.
`Program.printTyped` in `src/Effect4/Codegen/PrintTyped.lean` prints one expression.
Changing only the projected module would discard the retained generation relation.
The checked emission laws also consume that relation.

A proposed module connection reuses module assembly with a checked expression printer parameter.
Each definition uses its actual request environment and `sig.withDefs` signature.
The main expression uses its actual closed environment.
A named module erasure connector must relate the checked declarations to the existing ordinary declarations.
The existing expression erasure law supplies one part of that proof.
Hoisted layers require their checked contexts and a separate lift of the connector.
No existing hoist typing connector appears in the inspected tree.
The typed definition list currently retains the ordinary `.effs` template path.
The new tuple and pair type arguments also need exact erasure handling for their distinct head arities.

## Boundaries

The packet changes no production declaration, producer, helper, compiler option, semantics registry, or stored program representation.
No Lake command runs.
No claim establishes all possible helper signatures cannot work.
The findings reject the tested candidates and identify concrete consumers that a printer connection must serve.
No axiom gate check applies because this packet adds no Lean declaration.
