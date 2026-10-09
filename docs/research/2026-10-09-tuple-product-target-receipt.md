# Tuple product target blocker

The coordinator must retain the emitted annotation failure until a repair keeps the existing result inference controls compiling.
No helper implementation lands in this slice.
The final tree changes only finite compiler controls and research notes.

## Commits and scope

Base: `eba00d7857d692c23e82431480f0170e3e092ca0`.
Control head: `0e6b49d4b516b47c5f835c110aafe43fea42fbc8`.
Branch: `codex/tuple-union-result`.
This receipt follows the control head in a documentation commit.

| Path | Result |
| --- | --- |
| `harness/truth/literals.typecheck.ts` | Retained original bytes, plus seven exact type controls and fifteen negative controls |
| `docs/research/2026-10-09-tuple-product-target-plan.md` | Contract, ownership, and the final inference criterion |
| `docs/research/2026-10-09-tuple-product-target-receipt.md` | This evidence and its limits |

`src/Effect4/Machine/Term.lean`, `tools/Effect4Gen/PreludeAtoms.lean`, and `harness/truth/prelude-atoms.gen.ts` retain their base bytes.
The shared typed TypeScript printer remains unchanged.
No root, semantics registry, authority, compiler setting, or program representation changes.

## Checked blocker

`StreamArray.independent` emits a two-position tuple whose slots each contain a Chunk or End answer.
Its normalized result annotation lists the four tuple combinations.
The current helper returns a tuple of union-valued slots, which tsgo refuses at that annotation.
The retained `currentTupleRefused` and `currentPairRefused` controls reproduce that limitation.

A conditional Cartesian result satisfies the normalized annotation.
Widening precedes distribution in the retained proposal, and Boolean remains one arm.
The proposal retains nested generic payloads and the existing behavior for every other tuple arity.
The all-combinations control covers the four answer combinations.
Negative controls reject wrong payloads, invented tags, changed nested element types, mutation, and numeric singleton promises.

The following existing reader compiles with either current helper:

```typescript
Ref.modify(numericRef, state => tuple(optionAnswer, state))
```

Here `numericRef` holds a number, and `optionAnswer` has `Option.Option<number>`.
The proposed distributed result makes tsgo infer the callback answer as `None<number>`.
The compiler then rejects its `Some<number>` alternative.
`proposedTupleInferenceRefused` and `proposedPairInferenceRefused` retain that regression.

Both intersection orders satisfy the normalized annotation but fail the same inferred reader.
`NoInfer` on the result also fails that reader.
Pointwise-first overloads keep the inferred reader compiling but fail the normalized annotation.
Distributed-first overloads satisfy the annotation but fail inference.
The retained controls check each outcome directly.

An explicit downstream result type makes the proposed tuple reader compile.
The coordinator rejects requiring that extra author annotation as this repair.
The tested candidates therefore fail the final criterion.
This finite result establishes no impossibility theorem about other TypeScript declarations.

## Existing proof connection

No theorem is stated, changed, or proved.
The existing placement supplies the source connection, with the target connection still open.

| Placement field | Existing declaration and boundary |
| --- | --- |
| Concept and property | `store-typing`: normalization retains value membership |
| Question and role | `fits-normalize`, compatibility, in `tools/ProofGraph/Registry.lean`; pointer `Effect4.Program.Typed.fits_normalize` |
| Reach | `Fits w v t.normalize` iff `Fits w v t`; `fits_normalize_prod` and `fits_normalize_tuple` serve that claim |
| Exclusions | Source membership proves no TypeScript inference property or target simulation; decisions row 256 bounds direct-slot widening |
| Requirement | R4; the source law supplies membership transport, while this finite target annotation question remains open |

`Effect4.Program.Typed.fits_normalize`, `fits_normalize_prod`, and `fits_normalize_tuple` live in `src/Effect4/Laws/Program/Typed/Membership.lean`.
`Ty.normalize_tuple_pair` in `src/Effect4/Program/Ty.lean` connects the two-position tuple to product normalization.
Other tuple arities retain pointwise normalization under `Ty.normalize_tuple_of_ne` in that file.
The producer reads `NativeAtom.row.prelude` from `src/Effect4/Machine/Term.lean`.
`Effect4Gen.PreludeAtoms.entry` and `wide` in `tools/Effect4Gen/PreludeAtoms.lean` produce the helper and literal type rule.

## Commands and results

The compiler reports `Version 7.0.0-dev.20260629.1`.
The command uses the exact release installation through the ignored local dependency symlink.
Run the retained battery from `harness/truth`:

```sh
/Users/pooks/Dev/lean4-effect4/ts/release/node_modules/.bin/tsgo --ignoreConfig --target ES2022 --module ESNext --moduleResolution bundler --strict --exactOptionalPropertyTypes --noUncheckedIndexedAccess --verbatimModuleSyntax --allowImportingTsExtensions --noEmit --skipLibCheck --types bun literals.typecheck.ts
```

Result: exit zero, with every existing control and all retained blocker controls checked.
The fifteen `@ts-expect-error` controls require the named compiler refusals.
The seven exact type controls require the proposed product, arity, Boolean, and mixed-slot results.
No TypeScript settings change.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Machine.Term Effect4Gen.PreludeAtoms
LEAN_NUM_THREADS=3 python3 scripts/generate.py --only derived
```

Both candidate generator runs pass before restoration.
Only the prelude helper changes semantically in their generated output.
The second run also reveals an unrelated RunnerDerived header difference from `Effect4.Run` to `Effect4.Run.Basic`.
That out-of-scope header difference is restored, along with every candidate producer and helper change.
A fresh narrow build of the restored producer passes with thirty jobs.
No full battery or sweep runs.
No new Lean declaration requires an axiom gate; this slice reports no new axiom evidence.

A private copy of the coordinator's v2 emitted catalogue passes with the tuple-only proposal substituted.
Its existing SynchronizedRef readers keep `pair`, so that catalogue misses the tuple callback inference regression.
The retained minimized callback exposes the missing edge.
The actual production helper still has the original emitted annotation failure.

```sh
bun /private/tmp/effect4-tuple-identity.mjs
```

Bun reports version `1.4.2`.
Seven fixtures compare the current tuple body with the candidate identity body.
Every fixture retains item order, object identity, and serialized value bytes.
The current pair retains both input identities.
These are finite runtime checks, with no general host claim.

The strict language check and `git diff --check` pass before the control commit.
The receipt receives those same checks before its documentation commit.

## Next contract

Keep the normalized emitted result and inferred callback result as separate required observations.
Require one candidate to satisfy both, with the retained old helpers as positive inference controls.
A future target repair must explain how its generated annotation and result inference meet both observations.
It must retain Boolean widening, nested payload types, readonly results, and all existing caller checks.
It must establish no broader target claim from this finite battery.
