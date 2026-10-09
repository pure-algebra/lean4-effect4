# Checked product target printing receipt

Before merge: the public module printer still uses ordinary printing.
The catalogue retains its tuple refusal until the coordinator connects checked module printing under the existing certificate.
This slice repairs the connected expression route only.

Base: `d58d8d9d`.
Branch: `codex/checked-product-print`.
The old `codex/stream-array` branch remains intact.
The commit containing this receipt is the slice head.

## Change

Ordinary pair and tuple calls retain their existing first overloads.
Checked calls select a product overload through a different generic arity.
The typed term fold derives its slot arguments from the existing typing rule.
It inserts them only for a proper union in a two-slot call.
The pair argument uses a readonly target tuple of slots directly.
Its construction avoids normalizing that selector into a union of tuples.

`PrintEliminators.termAlg` and `PrintEliminators.termJoinAlg` share the slot condition in `src/Effect4/Codegen/PrintEliminators.lean`.
`EraseTermTypes.eraseProductJoin` removes only the named term shapes in `src/Effect4/Codegen/EraseTermTypes.lean`.
It leaves malformed generic arities, runtime arities and readonly selectors intact.
The operation row eraser retains its existing ownership boundary.
The ordinary reader still refuses the inserted term arguments before named erasure.

`NativeAtom.row` supplies the overload text in `src/Effect4/Machine/Term.lean`.
`Effect4Gen.PreludeAtoms.wide` supplies the shared product result in `tools/Effect4Gen/PreludeAtoms.lean`.
`harness/truth/prelude-atoms.gen.ts` is regenerated.
Its SHA-256 is `4153aa0c37e5bf2eec1ebd63f283883e48b7baba65aea1fc63ad1ab958aca921`.
A second producer run emits identical bytes.

The overload declarations use a function wrapper.
Their JavaScript text and function name differ from the old arrows.
They retain the existing return operations and assertions.
Finite execution checks selected values and nested handle reference identity.
This receipt claims no unchanged JavaScript body bytes or runtime theorem.

## Existing proof placement

| Field | Placement |
| --- | --- |
| Concept and property | exact-codecs; reconstruction through named erasure |
| Question and role | compatibility claims `typed-print-connector`, `typed-print-erasure`, `typed-print-read` |
| Pointers | `Program.printTyped_eq_print`, `Codegen.eraseJoinArgs_printTyped`, `Codegen.readTyped_printTyped` in `src/Effect4/Laws/Codegen/PrintTyped.lean` |
| Reach | the existing successful typed expression prints; lawful spelling and readable fragment remain premises where stated |
| Exclusions | no annotated-source admission, target typing theorem, whole-module reconstruction, allocation, codec or host agreement |
| Unlock | R8; the connected term stage before checked module production |

The existing statements remain unchanged.
`EraseTermTypes.eraseTerm_typedTuple` and `EraseTermTypes.eraseTerm_typedPair` serve `term_app_certificate` and the existing fold reconstruction.
`eraseProductJoin_hasCall` and `eraseProductJoin_call` transport the existing call invariant through the added local inverse.
The absence detector continues to serve `Program.printTyped_eq_print`.
No new registry claim or program representation enters the tree.

## Verification

The narrow build passes with 354 jobs:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Codegen.PrintTyped Test.Codegen.PrintTyped Effect4Gen.CatalogueExe
```

The focused battery checks both product helpers, named erasure, round trips and the raw-reader refusal.
It checks that `Ty.factors .never` retains a slot.
It checks that Option-valued callbacks retain ordinary inference.
The full union callback prints the checked row arguments too:

```ts
Ref.modify<number, number | string>(a1, (a2) => tuple<number | string, number>(a0, a2))
```

That full expression passes the target compiler.
A bare surrounding call, an incorrect cell type and wrong payloads remain red controls.
The target controls cover Boolean-plus-union slots, nested handles, retained never slots and old explicit generic callers.
The unchanged `harness/truth/literals.typecheck.ts` passes beside them.
Boolean distribution can repeat identical widened alternatives; the controls establish assignability, not literal type-list identity.

Run the generator twice and compare its output:

```sh
LEAN_NUM_THREADS=3 lake exe effect4gen-catalogue PreludeAtoms --group PreludeAtoms --imports Effect4.Program.NativeAtom --out harness/truth/prelude-atoms.gen.ts
```

This command runs the manifest group's producer directly.
It avoids generating unrelated outputs outside this slice.
The full derived-group gate remains a coordinator integration check.

The retained evidence directory contains `Audit.lean`, `Produce.lean`, target sources, settings, diagnostics, observations and hashes.
Run their Lean checks:

```sh
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-08-checked-product-print-evidence/Audit.lean
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-08-checked-product-print-evidence/Produce.lean
```

The three registry pointers and term reconstruction use only `[propext, Quot.sound]`.
The two new product inverse equations use only `[propext]`.
The two call transport helpers use only `[propext, Quot.sound]`.
The retained audit contains the exact output.

Both available installations use tsgo `7.0.0-dev.20260629.1`.
The first uses Effect `4.0.1`; the second uses Effect `4.0.0-rc.112`.
Bun `1.3.14` runs the finite JavaScript observations.
No lower TypeScript compiler or network installation runs.
Reproduce in fresh output directories:

```sh
python3 docs/research/2026-10-08-checked-product-print-evidence/reproduce.py --install /Users/pooks/Dev/lean4-effect4/ts/release --out /tmp/checked-product-release-replay
python3 docs/research/2026-10-08-checked-product-print-evidence/reproduce.py --install /Users/pooks/Dev/lean4-effect4/ts/eff --out /tmp/checked-product-pin-replay --helpers-only
```

Both helper batteries pass.
The release experiment compiles all twelve catalogue callers and matches the retained expected observations.
It also retains the wrong-sticky observation and the Effect 4.0.1 observations.
The original catalogue packet retains its sole `TS2375` at `streamIndependent.ts`.
The experiment changes that one call manually and uses the generated helper.
It is a finite design experiment, not public emitted acceptance.
The unchanged public facade remains a named follow-up.

`source-sha256.json` records source, evidence, package, compiler wrapper and Bun binary hashes.
The repeat generation and production `git diff --check` pass.
The staged check reports one final blank line in retained `catalogue-baseline/control.ts`.
Keep those baseline bytes unchanged.
No whole battery, module-public cutover, frozen Ref profile change, owner document edit or push runs.
No Lake process remains active in this worktree at handoff.
