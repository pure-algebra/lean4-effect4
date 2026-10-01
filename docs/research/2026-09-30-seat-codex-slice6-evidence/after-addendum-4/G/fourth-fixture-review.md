# G's fourth fixture: independent source review

The witness is relevant to G's stop rule: it selects a real, previously accepted layer term in the tree, from the exact file and lines addendum 3 included in its unchanged-leaf census. Its existing test checks printing only, so that test can remain green while the layer checker's verdict changes. It is not evidence that an existing printing assertion or an existing application `Api.typeOf` assertion will fail. No existing `Eff.provideLayer` wrapper around this sample has been identified or invented here.

This conclusion is source-grounded, not a fresh Lean result. Root still needs to compile `/private/tmp/GFourthFixtureProbe.lean` before treating the stated acceptance/refusal equations as checked. The draft probe has no concrete defect identified by this review.

Reviewed live worktree: `/Users/pooks/Dev/lean4-effect4-slice6`, HEAD `31e44efc6d695bf8d8c35df2df90b5bf300de924`. The relevant fixture, checker, native signature and G addenda are unchanged from `e5cc184b`; there are no current edits to the fixture/checker/native signature. This seat made no repository edits and ran no Lean, lake, build, make or generators.

## What the actual tree says

| Fact | Current source |
| --- | --- |
| The public list contains the effect leaf at index 1. | [TemplatesContract.lean:57](/Users/pooks/Dev/lean4-effect4-slice6/Test/Codegen/TemplatesContract.lean:57) declares `layerSamples`; line 58 contains `.effect key v`. |
| Its body returns unit, and its service key is name 7, type code 4. | [TemplatesContract.lean:23](/Users/pooks/Dev/lean4-effect4-slice6/Test/Codegen/TemplatesContract.lean:23) declares the native signature; lines 25–28 define `u = succeed(unit)`, `v = bind u (succeed(var 0))`, and `key = ⟨⟨7⟩, ⟨4⟩⟩`. |
| Native service type code 4 means nat at a free name. | [Native.lean:277](/Users/pooks/Dev/lean4-effect4-slice6/src/Effect4/Program/Native.lean:277), mapping `(4, .nat)` at line 278; [Native.lean:288](/Users/pooks/Dev/lean4-effect4-slice6/src/Effect4/Program/Native.lean:288) selects the code after excluding reserved names. |
| Current effect-layer typing does not compare the body's answer with the service carrier. | [Checker.lean:231](/Users/pooks/Dev/lean4-effect4-slice6/src/Effect4/Program/Checker.lean:231) checks the closed body and immediately returns its layer signature; [HasTy.lean:424](/Users/pooks/Dev/lean4-effect4-slice6/src/Effect4/Laws/Program/Typing/HasTy.lean:424) likewise has only the body's typing premise. |
| The present test checks the printer's refusal category, not typing. | [TemplatesContract.lean:69](/Users/pooks/Dev/lean4-effect4-slice6/Test/Codegen/TemplatesContract.lean:69) defines `isTableDefect`; line 83 only excludes that printing refusal over `layerSamples`. [Templates.lean:442](/Users/pooks/Dev/lean4-effect4-slice6/src/Effect4/Codegen/Templates.lean:442) defines `printLayerT` as the layer fold, not `Checker.checkLayer`. |
| The sample participates in the in-tree battery. | [Test/All.lean:84](/Users/pooks/Dev/lean4-effect4-slice6/Test/All.lean:84) imports `TemplatesContract`. |

The sample is distinct from the three exceptions: `leftWins` and `rightWins` are DocsOp merge layers at `dbKey` ([Provision.lean:607](/Users/pooks/Dev/lean4-effect4-slice6/src/Effect4/Program/Provision.lean:607)); the third fixture is the native Counter key with a string-returning body ([AuthorContract.lean:267](/Users/pooks/Dev/lean4-effect4-slice6/Test/Program/AuthorContract.lean:267)). This sample is the separate native name-7 key with a unit-returning body.

## Why the stop applies despite the printing-only test

The original G stop says to list any newly refused **in-tree program**, not only failing tests ([addendum 2:243](/Users/pooks/Dev/lean4-effect4-slice6/docs/research/2026-09-30-codex-brief-slice6-addendum-2.md:243)). Addendum 3 makes the relevant scope explicit: it claims every other **in-tree leaf** has matching carriers and specifically cites `TemplatesContract.lean:28,58` ([addendum 3:54](/Users/pooks/Dev/lean4-effect4-slice6/docs/research/2026-09-30-codex-brief-slice6-addendum-3.md:54)). Addendum 4 adds only the Counter/string fixture, then says a fourth refused in-tree program stops G ([addendum 4:76](/Users/pooks/Dev/lean4-effect4-slice6/docs/research/2026-09-30-codex-brief-slice6-addendum-4.md:76), rule at line 89).

Thus the authority record itself includes this raw `LayerTerm` fixture in the acceptance census. Calling its test printing-only does not remove it from that stated scope. The precise finding is a fourth expected **layer-checker refusal**, not a fourth test failure or a demonstrated change in execution.

## Probe review

`actualSample` reads `Test.Codegen.TemplatesContract.layerSamples[1]?`. `exact_source_sample` uses definitional equality to connect that actual entry to the explicit key/body. This handles the source's private helper names without guessing or replacing its fixture.

The probe also pins the actual signature to the native signature, the service carrier to nat, and the closed body's type to pure unit. The current acceptance theorem targets `Checker.checkLayer` on that same entry. The revised branch is the same G equation already used by the authorized `G/AuthorContractProbe.lean`: check the body, look up the key, then compare normalized answer and service types. Since this body contains no layer and is independently well typed, using the current `Checker.check` for the body does not omit any recursive G change or alter the refusal ordering relevant to this fixture.

Expected root-leaf refusal:

```lean
.error ⟨[], .valueNotSubtype (⟨⟨7⟩, ⟨4⟩⟩ : ServiceKey) .unit .nat⟩
```

The body checks at `[0]`; the value-to-service mismatch is located at the layer leaf `[]`. It is not an unknown-key or literal-alphabet refusal. The probe retains both direct-leaf and source-selected acceptance/refusal equations and prints the axioms of all ten named theorems.

## Minimal proposed owner amendment

> G may additionally refuse the existing `Test.Codegen.TemplatesContract.layerSamples[1]?` entry: `.effect ⟨⟨7⟩, ⟨4⟩⟩ (.bind (.succeed (.lit .unit)) (.succeed (.var 0)))`. Its expected refusal is `valueNotSubtype key unit nat` at `[]`. Keep this printer-coverage sample and its shared `u`, `v`, and `key` definitions unchanged. Add a negative checker control tied to that exact public list entry in G's `LayerValue` battery, and retain the neighboring nat-valued succeed entry as a positive control. Addendum 3's assertion that every listed leaf has matching number/Boolean carriers is corrected for this entry. The previously authorized three fixture changes remain as specified; any additional newly refused in-tree program or layer beyond the gap programs and these four named exceptions still stops G.

This adds one expected refusal. It does not widen the checker, change the service carrier, rewrite a shared printer fixture to conceal the change, or require a generated-file amendment. The proposed post-G controls are in `/private/tmp/GFourthFixtureControls.proposed.lean`; they must not be treated as current-tree passing tests. This is a proposal only, not authorization to continue G.

Serial verification owed, from the slice6 worktree:

```sh
lake env lean -DwarningAsError=true /private/tmp/GFourthFixtureProbe.lean
```

After an owner amendment and G implementation, check the proposed controls against the actual checker rather than the local revised equation, and rerun `TemplatesContract` to confirm the retained printer contract still passes. The rest of G's required laws, negative controls, and corpus check remain unchanged.
