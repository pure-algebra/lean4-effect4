# T5 literal repair review

## Result

The captured active repair follows decisions row 256. No new actionable source defect was found.

This is source review, not acceptance. Seat HEAD is `98b56e62`; the changed files are uncommitted in the captured snapshot.

Main authority is `e6d63ddb`. The review does not chase later edits or claim a current compiler, generator or runtime result.

## The literal boundary

`NativeAtom.row` in `src/Effect4/Machine/Term.lean` remains the owner of the `pair` and `tuple` bodies.

Each body uses one direct type assertion. The shared `Wide` alias has one source owner in `tools/Effect4Gen/PreludeAtoms.lean`.

`Wide<T>` widens immediate number and Boolean types. It preserves string literals and performs no recursive rewrite.

The active generated prelude has matching helper bodies and the one alias. This textual agreement does not replace the owning generation check.

`NativeAtom.spec` changes explanatory text only. `litArgTy` and the Lean value/type rules are unchanged.

The source explicitly records loss of direct numeric and Boolean singleton types and brands. It also records loss of Boolean-tag discrimination.

Those consequences are already ruled in row 256. They are not new scope changes or undisclosed compatibility claims.

## The six pins

The changes in `harness/truth/tuples.typecheck.ts` are exactly these six existing pins:

| Pin | Previous expectation | Active expectation |
| --- | --- | --- |
| `singleton` | `readonly [7]` | `readonly [number]` |
| `pair` | `readonly [7, "x"]` | `readonly [number, "x"]` |
| `larger` | `readonly [7, "x", true]` | `readonly [number, "x", boolean]` |
| `first` | `7` | `number` |
| `third` | `true` | `boolean` |
| `nested` | `7` | `number` |

The second string position remains `"x"`. Existing supplied-union tuple projections retain their literal expectations.

Two added refusals target the constructor’s own number and Boolean projections. Wider result annotations alone would not detect the old inference policy.

## Positive and refusal domains

The new `literals.typecheck.ts` covers both constructors through exact-type assertions and negative assignments.

It checks empty and mixed tuples, direct scalar widening, string-variable identity, string-tag discrimination, positions and readonly structure.

It also checks supplied nested tuples, lists and records without recursive rewriting.

Ref and Deferred handles retain their invariant parameters. Negative assignments and writes exercise value and error parameters separately.

The final section checks the deliberately lost Boolean discrimination and brands, while a brand nested inside a supplied record stays.

`term-rows.typecheck.ts` removes the three registered-difference directives: rate-limiter request, probe take and flagged fold.

Those cases become positive controls. Additional singleton assignments must remain refused.

These are source-confirmed control definitions. They have not been compiled by this monitor during this review.

## Wiring and reuse

The control file is included by `harness/truth/tsconfig.json`, copied by `scripts/check-truth.py` and listed in the Makefile truth prerequisites.

This uses the existing compiler lane. No parallel checker or new acceptance ranking appears.

The active `run-truth.ts` also derives atom imports from `atomNames` instead of its old handwritten list.

The non-atom helpers remain named separately. This is a useful inventory reuse, but it changes generated module headers beyond the two helper signatures.

The seat’s eventual receipt must distinguish that generation change from the literal repair. Existing truth generation and compiler checks are its acceptance route.

No new gate or sweep is requested by this review.

## Row 257 stays separate

The literal repair changes target helper inference. It does not prove the Queue’s five general typing goals.

Row 257 gives QTYPES those unchanged goals and gives the public wrapper its actual checker evidence through existing admission.

Nothing in the captured literal edits replaces those goals, supplies a proof assumption or changes the Queue’s arbitrary-type promise.

## Retained evidence and remaining acceptance

The earlier decision-probe packet used pinned tsgo `7.0.0-dev.20260629.1` against rc.112.

Its retained receipt distinguishes the baseline, revised pins, exact candidate, string-widening mutant and emitted helper JavaScript comparison.

That packet reports byte-identical helper JavaScript for its compared inputs. This review does not extend that result to every active generated artifact.

The captured T5 receipt describes earlier part A work and the original literal finding. It is not a receipt for this active repair.

The owning seat still needs its current narrow generation/compiler results and final receipt, including the real application modules required by the brief.

A passing fragment or old scratch compiler output cannot stand in for that acceptance.

## Completion boundary

All reviewed source files have retained hashes. The receipt records whether a source changed after the snapshot.

No repository edits, Lean checks, compiler runs, runtime runs, generators, installations, dispatches or Claude messages occurred.
