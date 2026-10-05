# OCaml lowering scouting

Reviewed main: `182312f30194f0beefa7a6273eb1144aa834c0f0`.
Evidence: source inspection and finite OCaml 5.1.1 interpreter controls.
Proof role: proposed connecting obligations.
Scope: three small slices, without a new backend or scheduler.
No repository changed. No Lean, dune, generator, installation, or active build ran.

## Recommendation

First confirm and repair builtin binder capture on the actual lowering route.
The framing cleanup can proceed independently after coordinator ownership checks.
Retain the power optimization as a separate numeric-profile slice.

The UTF-8 precedent already landed at `93c3dfad`, integrated at `eef851b5`.
Its receipt records standard-library reuse and finite comparisons, not a new Lean theorem.
`Lean.SCC.scc`, native constructor sharing, `Map.Make(Int)`, and abstract carrier functors already exist.
Do not propose these as new improvements.

## 1. Make builtin expansions fresh

Source: `builtin?`, `applyBuiltin`, `preUsed`, `fresh`, `bindVar`, `argExpr?`, and `letValueExpr` in `src/OCaml5/Lcnf/Translate.lean`.
Also read `snake` and `localName` in `src/OCaml5/Lcnf/Naming.lean`.

`Nat.mul` introduces `_mula` and `_mulb` directly.
`Nat.shiftLeft` introduces `_shift_scale` directly.
Under-application introduces `_b1`, `_b2`, and subsequent names directly.
`List.contains` introduces `_elem` directly.
These names do not pass through `fresh` and are absent from `preUsed`.

A simple source binder name `_mula` remains `_mula` through `components`, `snake`, and `localName`.
`bindVar` uses that name when it is unclaimed.
`argExpr?` then returns the corresponding variable without renaming.
The builtin call path passes those arguments into the fixed-name expansion.
Thus the name supply does not establish freshness for every builtin-introduced binder.

The retained host controls mirror these exact expansion shapes:

| Operation | Arguments | Capturing expansion | Fresh-name control |
| --- | --- | --- | --- |
| Multiplication | `x = 3`, source local `_mula = 5` | 9 | 15 |
| Partial addition | captured source local `_b1 = 3`, later argument 5 | 10 | 8 |
| Shift left | source local `_shift_scale = 3`, shift 2 | 16 | 12 |

These are constructed translation-input witnesses.
They are not a freshly compiled Lean source counterexample.
The immediate prerequisite is a persisted-LCNF fixture showing the supplied names at the builtin call.
No active machine miscalculation is claimed.

Smallest repair: allocate each introduced binder through the translator's shared name supply.
Preserve evaluation count, operand order, partial application, and existing refusals.
A larger string blacklist alone leaves future builders exposed.

Proposed placement: `translation-simulation`, R8's existing typed-lowering open part, decisions row 28.
Proposed property: builtin translation preserves operand denotations under an environment that represents the LCNF arguments.
Required hypotheses include arity, the scalar profile, primitive agreement, and freshness against free operand names.
Consumer: `letValueExpr`, then `translateDecl` and the emitted API and engine closures.
Observation: result or exception, plus callback order where a builtin accepts a function.
Exclusions: compiler erasure correctness, arbitrary host callbacks, whole-machine agreement, and unbounded numeric exactness.

Use `SemanticsTarget.TEnv.find?`, `evalT`, and `applyT` for the scoped substitution argument.
Those definitions exist; this review found no ready general freshness theorem.
Keep the primary obligation in the existing theory and add only the connecting helper it needs.
Acceptance needs a name-collision fixture, an ordinary-name control, and alpha-renaming invariance.
Run the exact emitted OCaml module when the assigned seat owns the build lane.

Ownership: translator and its focused controls; generated files change only at coordinated regeneration.
T3b's target acceptance recently completed in its seat; integrate or freeze that base first.

## 2. Remove the duplicate framing implementation

Source: `ocaml/engine/e4_be.ml`, its interface, `ocaml/eff/eff_frame.ml`, and `ocaml/engine/dune`.

The engine already depends on `effect4_eff`.
The older reason for copying framing, `E4_be` interface D1, no longer applies.
The dune comment already says the engine forwards, but the implementation still transcribes framing.

The strongest first slice is delegation, not a new byte algorithm.
Share frame reading and natural-digit writing with `Eff_frame`.
Retain the checked `E4_be.read_be64` wrapper because the underlying reader assumes a valid window.
Retain negative-input exceptions, exact framing, and trailing-byte refusals.
Do not send invalid offsets directly into the unchecked reader.

The isolated probe compares both current frame readers over ordinary and extreme windows.
It also compares current big-endian writing with the installed standard primitive.
It passes 9,757 assertions in OCaml 5.1.1 with 63-bit integers.
This includes the hygiene controls above and explicit integer-overflow refusals.
This evidence is finite and does not certify all inputs.

Optional follow-up: replace repeated fixed-width byte loops with `Buffer.add_int64_be`, `Bytes.set_int64_be`, and `String.get_int64_be`.
These functions exist in the installed compiler's standard library.
Keep nonnegative bounds before conversion and unsigned-high-bit refusal after reading.
The framing profile remains 63-bit; this proposal does not silently add 32-bit portability.
`emit_be64` has internal callers with nonnegative lengths; preserve or explicitly document that premise.

Proposed placement: `exact-codecs`, R8's face connection, serving the canonical wire.
Proposed property: each admitted host framing operation equals its Lean byte operation.
Reuse `be64_eq_shifts`, `natOfDigits_be64`, `be64_natOfDigits`, and `natOfDigits_natBytes` in `src/Effect4/Store/Carrier/Digits.lean`.
Reuse `framed_length` and `framed_inj` in `src/Effect4/Store/Carrier/Val.lean`.
The host primitive contract remains an external assumption until a checked connector supplies it.

Consumer: `E4_program`, CAS framing, wire admission, and the engine's canonical hashing inputs.
Observation: exact bytes, decoded natural, next offset, or refusal.
Hypotheses: valid window, payload length in range, and the selected host integer profile.
Exclusions: schemas, arbitrary target execution, compiler correctness, and allocation failure.
Acceptance reuses `ocaml/eff/test/test_frame.ml` and `ocaml/engine/test/test_math.ml`.
Retain malformed UTF-8, invalid windows, leading-zero naturals, high-bit lengths, and unchanged goldens.

Ownership: hand framing modules and their existing tests.
No LCNF regeneration is necessary for this first delegation slice.
This is the clearest independent cleanup analogous to the earlier UTF-8 work.

## 3. Reuse the already-tested power algorithm in emitted code

Source: `powClamped` in `src/OCaml5/Lcnf/Translate.lean` and `pow` in `ocaml/engine/e4_nat.ml`.

The emitter still produces recursive work proportional to the exponent.
`E4_nat.pow` already uses a tail loop and stops when its result reaches a fixed point.
Its `pow_reference` transcribes the emitter's current recurrence.
The existing math test compares both on small inputs and checks huge fixed-point cases.

The retained interpreter control runs `1 ^ 1,000,000` through both functions.
Both return 1; the ordinary `2 ^ 10` control returns 1024.
No stack overflow occurred, so this review claims no stack-overflow defect.
The opportunity is to remove needless recursion while retaining the current bounded operation.

Proposed placement: `translation-simulation`, R8's numeric-profile open part, decisions rows 28 and 108.
Proposed property: the emitted bounded-power algorithm agrees with its saturated recurrence for nonnegative host operands.
Then prove the separate exact-range law against Lean natural exponentiation.
Consumer: the `Nat.pow` and `Nat.shiftLeft` builtin rows.
Hypotheses: the recorded 63-bit bound, nonnegative operands, and exact host multiplication below the bound.
Observation: answer and termination within a stated work bound.
Exclusions: accepting saturation as Lean equality outside the profile and the whole numeric migration.

Prove the recurrence's fixed-point lemma before reusing the optimization.
Reuse `E4_nat.pow` and `test_math` controls rather than designing another algorithm.
The current row 108 refusal requirement still needs its own implementation; this cleanup does not close it.
Fix builtin freshness first, because a new emitted loop adds binders.
Keep the emitter standalone; avoid making `ocaml/gen` depend on the engine library.

## Current checker limits

The historical idioms receipt names `scripts/test-generators.py` and its fixtures.
Those paths are absent at this reviewed HEAD.
The tooling cleanup at `75e2c9aa` removes the broad generator harness.
Do not cite its historical run as a current standing check.
Add only the focused builtin fixture to the current tool/test arrangement.
Do not restore a broad removed framework without a demonstrated need.

`Ml.checkModule` checks syntax and names, not captured-variable semantics.
OCaml functor checking catches carrier type mismatches, but a capturing arithmetic expression can still type-check.
The compiler and standard library provide valuable static checks and trusted operations.
They do not automatically prove the source-to-target connection.

## Receipt

`receipt.json` retains source hashes, commands, exact outputs, and limits.
`probe.ml` loads the two actual framing modules and executes the finite comparisons.
Its hygiene functions mirror the translator's relevant target expressions.
`probe-pow.ml` loads the actual `E4_nat` module and checks its two algorithms.
Both use the installed OCaml interpreter, with no compilation or build claim.
