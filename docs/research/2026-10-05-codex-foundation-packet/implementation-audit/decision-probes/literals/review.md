# Literal-type decision probe

Recommend shallow widening of numeric and Boolean slots in `pair` and `tuple` for the generated Effect target. Preserve string literals. Preserve every non-primitive argument's existing type. Do not recursively rewrite records, lists or handles.

This packet freezes main `368e0314031cdc2376c38d5738bcb3cde4d099e0`. It changes scratch files only. The compiler is tsgo `7.0.0-dev.20260629.1`; Effect is `4.0.0-rc.112`. No Lean, generator, installation, application execution or repository edit occurs.

## Exact decision

The saved T5 proposal uses `Wide<T> = T extends number ? number : T extends boolean ? boolean : T`. Its two constructors retain `const` parameters and return tuples whose immediate slots use `Wide`.

The exact proposal passes the retained application controls. The same signatures also compile with direct return assertions. Neither helper needs the proposed intermediate `as unknown as` escape. One construction-local assertion remains in each helper. These assertions are not a proof of target agreement.

The policy applies to numeric and Boolean subtypes, including variables and brands. It does not apply only to literal expressions. The probe confirms that a numeric or Boolean brand in a direct slot disappears. A brand inside an existing record remains. This boundary matches the represented `nat` and `bool` types; it must not become a general TypeScript normalization policy.

`litArgTy`, in `src/Effect4/Program/Typing/Rules.lean`, already assigns every natural and Boolean literal its broad type. It retains a direct string literal under a const-generic atom. No Lean literal rule change is proposed.

## Checked results

| Isolated input | Result |
| --- | --- |
| Current helpers, exposed registered differences and retained real Queue take | 15 diagnostics: three small controls and twelve take diagnostics |
| Exact saved selective-widening proposal, revised tuple pins | Accepted |
| Same selective policy with direct assertions | Accepted |
| Current helpers with explicit outer Ref callback return types | Same 15 diagnostics |
| Selective policy plus string widening mutant | Six diagnostics, including broken tagged-union narrowing |
| Minimal current pair choice and fold | Two diagnostics |
| Same minimal inputs with selective policy | Accepted |
| New negative controls without suppression comments | Thirteen expected diagnostics |
| Current and revised helper JavaScript | Byte-identical, 80 bytes |

The small failure is `ite(flag, pair(true, 0), pair(false, 0))`. The current compiler infers the first pair as `[true, 0]`. It then rejects `[false, 0]`. Declaring the result as `[boolean, number]` does not fix that inference.

The fold control starts at `tuple(0, false)` and returns `tuple(number, true)`. Its current inferred accumulator is `[0, false]`. The selective policy admits the intended `[number, boolean]` accumulator.

The exact retained `takeStep.txt` expression appears unchanged in `real-queue-take.ts`. Only its import header and surrounding declared input/output types are added. The receipt checks these bytes. The expression is prior generated output, not a new generator run. Existing committed `term-rows.typecheck.ts` supplies the rate-limiter request and initial take attempt.

## Boundaries retained

The accepted controls retain string tuple discriminants, string record tags, nested constructor results, readonly positions and exact tuple length. They retain the broad type of an already broad string variable.

`Ref<1>` and `Deferred<true, "E">` retain their exact parameters through both constructors. Assigning wider handles still fails. Writing a different Ref value or completing the Deferred with false still fails.

A nested call such as `tuple(tuple(1, "Tag"), true)` widens each constructor's primitive slots. A supplied `readonly [1, true]` remains that supplied type. There is no recursive widening.

Numeric and Boolean singleton precision intentionally disappears. Boolean tuple tags therefore lose discriminant correlation. String tags retain it. The owner should approve this exact consequence.

## Smallest landing

Keep `NativeAtom.row` in `src/Effect4/Machine/Term.lean` as the body owner. Keep the generated prelude as output. Put the shared type alias in the existing `PreludeAtoms.render` preamble, or use an equally local generated spelling. Keep one policy owner.

Update the three tuple construction pins and their three dependent projection pins: `singleton`, `pair`, `larger`, `first`, `third`, and `nested`. The saved note mentions only the three initial errors. Updating those exposes the projection pins too.

Move the three registered differences to positive controls. Retain the tagged-union, invariant-handle and readonly refusals. Keep the exact full Queue take control alongside its small fold reproducer.

The annotation-only alternative adds explicit outer callback result types. It fixes neither the limiter nor the nested Queue folds. It is not a useful replacement for this policy.

## Placement and evidence

This is finite target type-checking evidence for the existing TypeScript face boundary under R8. It is not a new proof obligation or a claimed compiler theorem. The consumers are the printed rate-limiter request, Queue take, and ordinary tuple terms.

The hypotheses are the pinned compiler and Effect package, the recorded strict configuration, and the generated atom profile. The observation is compiler acceptance or a named refusal. The emission comparison observes only helper JavaScript bytes. It says nothing about application execution, scheduling, cancellation, host replies, or general compiler correctness.

The immediate prerequisite is the owner's target-policy ruling. The owning implementation must regenerate its outputs and perform the relevant narrow acceptance. This packet does not ratify or implement the change.

## Reproduction

Run `python3 run.py baseline exact-candidate revised contextual blanket-mutant minimal-baseline minimal-revised refusal-observations` from this packet. Every compiler command and working directory is recorded in `outputs/runs.json` and the final receipt. Run `python3 emit.py` for the helper emission comparison. Both scripts use the existing absolute tsgo path and scratch directories only.
