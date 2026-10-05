# Builtin table: primary-source review

Status: advisory. Evidence: source inspection and official documentation. No compiler, build, benchmark or generator ran.

Reviewed source: main `182312f30194f0beefa7a6273eb1144aa834c0f0`.
Installed configuration: OCaml 5.1.1; `Makefile.config` sets `FLAMBDA=false`.

## Recommendation

Accept the first-order builtin table refactor. Preserve direct primitive nodes for arithmetic and equality. Use named support definitions for compound rules where they simplify the contract. Eta binders handle missing arguments. Fresh generation or a derived reserved namespace must establish disjointness from free variables. Do not base acceptance on predicted inlining.

The table can share operation identity, arity, argument permutation, support-definition dependency, and admitted-domain metadata. OCaml spellings and primitive meanings remain target-specific. A later TypeScript backend needs its own primitive interpretation and agreement checks.

## Checked claims

| Claim | Finding | Smallest correction |
| --- | --- | --- |
| A named polymorphic equality helper loses specialization | Plausible, but too broad as a blanket performance claim. Installed `Stdlib.(=)` is `%equal`. Current upstream `translprim.ml` specializes comparisons from operand types. The pinned implementation could not be fetched. | Preserve primitive syntax without promising faster code. Measure the exact generated program in an authorized later slice if performance matters. |
| `Stdlib.max` can inline across modules without Flambda | Supported as a capability. The OCaml 5.1 manual describes cross-module information in `.cmx` files and classic inlining. Installed `max` is an ordinary function. | Say it may inline. Availability of `.cmx`, `-opaque`, thresholds and call shape matter. Inlining does not imply recovery of type specialization. |
| Hygienic eta expansion solves partial-application typing | Supported conditionally. Explicit function values can regain generalization under the value restriction. | Check the actual generated bindings at two type instantiations. Preserve captured arguments and evaluation timing. |
| One support definition can serve the printer and target evaluator | Good way to remove duplicated algorithm bodies. It does not independently validate that body against Lean operations. | Retain source-side oracle cases and actual emitted-OCaml execution. Keep primitive interpretation independent. |

## Present-domain limits

`builtin?` maps scalar equality for Nat, UInt8, UInt64, USize, Bool and String. Those rows do not admit arbitrary functions or floating-point values. The list emptiness row compares a list with `[]`; do not replace it with general element comparison.

OCaml equality and ordering raise on functional values and may diverge on cyclic structures. `compare` and equality differ on NaN. `min` and `max` have unspecified NaN results. These are limits on a future broad comparison contract, not demonstrated faults in the present integer-only min/max rows.

`Conform.Lcnf.Target.applyPrim` currently models equality through `TValue.beq`. It does not implement OCaml's exception behavior for functions. Therefore a generic support API must retain an admitted comparison domain. Existing scalar callers do not establish arbitrary-value agreement.

`argExpr?` produces only a variable or an erased omission. However, the builtin branch of `letValueExpr` uses `argAsList`, which can call `useAsList` and emit a carrier-to-list conversion. Ordinary unseamed arguments are variables; the complete builtin path does not guarantee values. Eta expansion or affine substitution that moves, omits, or branches around a conversion requires its totality and purity contract. The observation must exclude allocation and cost, or account for them explicitly. Otherwise, bind the conversion once at the original evaluation point. This is an acceptance premise, not an established reachable defect. OCaml does not specify ordinary application argument evaluation order.

Preserve the supplied equality function in `List.elem` and `List.contains`. The latter intentionally places the searched value before the list element. Existing asymmetric-comparator controls protect this. Builtin `&&` and `||` have short-circuit syntax; ordinary unseamed operands are already variables, but the complete path also needs the conversion contract above.

## Narrow obligations and checks

Proposed placement: `translation-simulation`, R8 typed lowering. R6 remains the host lane. Proposed claim: builtin lowering agrees on the admitted primitive domain. Consumer: the LCNF translator and existing Conform compiler profile.

First prove or check table structure: unique source names, valid argument indices, declared arity, closed support definitions, and dependency completeness. These finite properties do not establish operation semantics.

Then connect each compound support body to its source operation. Hypotheses include the numeric representation, admitted operand types, atomic arguments or admitted pure total carrier conversions, capture-disjoint binders, and a sufficient evaluation budget. Observe value, exception, refusal and frontier separately. Exclude whole-compiler correctness and arbitrary OCaml values. Immediate prerequisite: freeze the row descriptor and support-body interpreter.

Keep native controls for exact application, under-application, over-application, captured values, and two type instantiations. Reuse zero division, zero modulus, shifts, clamp, UTF-8 and asymmetric comparator controls. A wrong argument permutation and an eta-capture mutant should fail. These are finite controls until connected by a theorem.

Lean's `decide` can prove closed decidable table properties by reduction. This is distinct from a successful `#eval` report. `native_decide` adds compiler trust and conflicts with this repository's trust rule. Use ordinary kernel-checked proofs or the existing checker mechanism; do not add another validation framework.

## Primary references

- [OCaml 5.1 native compilation](https://ocaml.org/manual/5.1/native.html): `.cmx`, `-opaque`, and `-inline`.
- [OCaml 5.1 Flambda documentation](https://ocaml.org/manual/5.1/flambda.html): classic inlining limits and distinction from Flambda.
- [OCaml 5.1 polymorphism](https://ocaml.org/manual/5.1/polymorphism.html): value restriction and eta expansion.
- [OCaml 5.1 expressions](https://ocaml.org/manual/5.1/expr.html): application evaluation order.
- [OCaml 5.1 Stdlib](https://ocaml.org/manual/5.1/api/Stdlib.html): comparison domains, NaN and short-circuit Boolean operations.
- [OCaml current translprim implementation](https://github.com/ocaml/ocaml/blob/trunk/lambda/translprim.ml): type-directed primitive specialization. This is corroboration from current upstream, not pinned 5.1.1 evidence.
- [Lean tactic documentation](https://lean-lang.org/doc/api/Init/Tactics.html): `decide` proof reduction and native evaluation trust. This documentation is current; the project pins Lean 4.33.1.

Pinned installed sources are hashed in `receipt.json`. The failed pinned source download is recorded in `download.json`. No assembly or runtime performance result is claimed.
