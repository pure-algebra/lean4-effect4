# Conformance semantics: small API upgrades

Status: advisory source review at `182312f30194f0beefa7a6273eb1144aa834c0f0`.
Evidence: static source assertions and installed OCaml 5.1.1 library inspection. No Lean, OCaml, build, generator or installer ran.

## Recommendation

Reuse the existing source and target interpreters. Add only the library calls and labelled forms that the selected builtin rows require. Keep their primitive meanings independent.

The coordinator already plans common support assembly and a support-body mutation reaching both interpreted and native output. Do not repeat that finding as unaddressed.

## What already works

`Target.evalT`, `applyT` and `applyNamed` support named helpers, captured local functions, partial applications, surplus arguments, and recursive top-level calls. `LcnfMl.ofExpr` already reads their ordinary application and function syntax. A new general helper evaluator is unnecessary.

`Normalization.main` already checks source interpretation, target interpretation, and actual emitted OCaml through the compiler profile. `Fixture` joins those observations under common case names. Keep that driver and extend its fixture construction.

`CompilerControls.evaluate` is a small expression helper. It currently uses an empty program and a caller-local `max_int`. Let it consume the common support program and profile constants when the new helpers need them. A helper starts with its own parameters; it does not inherit that caller environment.

The source interpreter is intentionally different. `applyValue` requires saturated local LCNF calls, and `applyPrim` refuses non-saturated primitive calls. Use named Lean wrappers for source-backed partial-application fixtures. Do not treat a source-interpreter limitation as a target counterexample.

## Immediate upgrades

| Need | Existing boundary | Smallest extension |
| --- | --- | --- |
| Target-only value and exception controls | `TCase` expects only a value. `differentialT` calls every target exception a counterexample. | Add an expected target observation with value and named exception cases. Reuse `runT`, subjects and report rows. Keep exhaustion unresolved. |
| `Option.getD` | `builtin?` emits `Option.value` through `Ml.Expr.appL`; `ofExpr` refuses every labelled application. | Admit the exact emitted `Option.value` call shape with its one positional option and required `default` label. Keep other labels and optional arguments refused. |
| Callback library calls | The builtin table emits nine callback names absent from `primArity`. | Add only names reached by the chosen rows; invoke callbacks through existing `applyT`, with fuel and outcome propagation. |
| Accurate unsupported status | `TOutcome.stuck` combines absent rules and wrong value shapes. `differentialT` maps all to refused. | Optionally distinguish structured unsupported reasons from malformed values, then reuse the report adapter. Both current outcomes fail closed. |

The nine existing callback spellings are `List.exists`, `List.map`, `List.filter`, `List.fold_left`, `List.for_all`, `List.find_opt`, `List.filter_map`, `Option.map`, and `Option.bind`. Their absence is a measured support gap. It is not evidence that current normalization inputs reach every row.

Start with `List.exists` if the selected controls include the existing asymmetric `List.contains` case. Add map, fold or option callbacks only when the selected support or fixture requires them. `List.elem` also passes a partially applied comparator, so its adapter should call `applyT` rather than inspect closure representation itself.

Do not erase labels indiscriminately. The exact Option adapter must preserve required-label matching, eager evaluation of both supplied arguments, and the admitted argument evaluation contract. A branch that evaluates the default only for None would change the target call. Carrier conversions require the purity and totality premises already stated in the builtin packet. Arbitrary optional arguments, label omission, reordering and partial labelled applications remain excluded until specified.

## What to share

Share support assembly, dependency validation, case identifiers, expected-outcome comparison, report construction, and the target's existing closure application operation. Keep one implementation of target callback application.

Keep `Conform.Lcnf.Prim.apply` and `Target.applyPrim` semantically separate. Source naturals, target words, source strings and target byte strings deliberately differ. One implementation of both answers would conceal the difference the differential measures.

Sharing one support syntax body between emission and target reading removes copied algorithms. It does not supply the independent Lean expectation. Retain source-computed results and native controls. The planned support-body mutation should test the shared body, while an operand-order mutant tests the source-to-target connection.

Current UTF-8 helpers form an explicit exception: `primitivePrelude` appends raw bodies only during emission. The target interpreter uses named primitive assumptions. Native controls test the actual implementation. The new assembly design addresses this boundary; its report should continue naming any remaining assumptions.

## Controls and proposed obligations

A target-only control is still finite evidence. Record `.tested` after execution. Use the existing `Evidence`, `Outcome` and `Obligation.Status` types. Inspection provenance and a control's role are separate metadata; neither `inspected` nor `control` is an accepted Evidence spelling. A proved label needs its actual theorem and axiom evidence.

Keep these controls small:

- A named helper captures no caller-local constant accidentally.
- A callback reads a captured value and returns the expected mapped result.
- The asymmetric equality callback preserves argument order.
- Exists and find stop before a later callback that raises.
- A callback exception propagates; a fuel frontier stays unresolved.
- Option.value selects Some or the supplied default, while evaluating the supplied arguments according to the admitted call contract.
- A missing helper or unsupported label fails visibly.

Proposed placement: `translation-simulation`, R8 typed lowering. Consumer: the selected builtin rows and Conform compiler profile. Required property: the selected target library adapter and reader preserve their admitted operation observation. Hypotheses: resolved library name, related operands, callback agreement, scoped captures, the labelled-call contract, and sufficient related budgets. Observation: result or named target exception; refusal and fuel frontier remain distinct. Exclusions: arbitrary OCaml, arbitrary effectful callbacks, exact allocation cost, whole-compiler agreement, and R6 host admission. Immediate prerequisite: select the reached rows and freeze the adapter domain.

## References and retained evidence

- Source declarations: `Target.applyT`, `Target.applyNamed`, `Target.differentialT`, `LcnfMl.ofExpr`, `Normalization.main`, and `CompilerControls.evaluate`.
- Installed source: OCaml 5.1.1 `list.ml` and `option.ml`; hashes are retained in `source-evidence.json`.
- [OCaml 5.1 Option contract](https://ocaml.org/manual/5.1/api/Option.html).
- [OCaml 5.1 List contract](https://ocaml.org/manual/5.1/api/List.html).

`source-evidence.json` records nine callback-name checks and eight existing-boundary controls. They are source assertions, not interpreter or compiler executions.
