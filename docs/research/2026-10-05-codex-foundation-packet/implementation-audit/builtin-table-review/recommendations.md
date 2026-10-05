# Builtin table: landing guidance

The owner authorizes the table refactor. Keep that authorization distinct from the broader lowering architecture in decisions row 29.
Reviewed source: main `182312f3`. Evidence: source inspection and three independent scouts; no new build or generator run.
The live design is still changing. These are acceptance recommendations, not findings against an implemented new table.

## Direction

Use row data and the existing OCaml syntax for support definitions.
Keep simple operator forms inline where their contract permits it.
Use named support definitions for binding-heavy forms.
Do not require a new general template language or another program representation.
Store semantic domains separately from backend spellings, evidence status, and cost claims.
The same semantic contract can later receive a TypeScript implementation; OCaml support code is not automatically that implementation.

## Immediate corrections to the design argument

1. Binder-free, affine substitution is not a complete call-by-value preservation condition.
   A parameter used zero times disappears. A parameter used in one conditional branch becomes conditional.
   Short-circuit operators can also skip an argument. Rearranged arguments can change evaluation order.
   `Translate.argAsList` can insert carrier conversions, so supplied expressions are not always variables.
   State totality, purity, and the observation for those conversions, or sequence supplied expressions explicitly.
   Hoisting an expression outside an eta-expanded function also needs that contract; it changes when evaluation occurs.
   Value agreement can exclude allocation and cost. It must not claim unchanged evaluation count from linearity alone.

2. Computed reserved eta names can work; freshness need not mean a new spelling at every site.
   Require disjointness from actual argument free names at every entry point, after source names are allocated.
   Check builtin, extern, and wrapper paths. `ExternFn.apply` currently introduces fixed `_exN` names separately.
   Support globals, ordinary generated globals, and extern head/dependency names also need protection.
   A final validator can refuse remaining collisions. That establishes rejection, not successful translation of every old input.

3. The existing conformance path must consume the support definitions.
   `Normalization.main` currently builds the target program from `translated.decls`; emission prepends its prelude separately.
   `LcnfMl.ofExpr` converts recognized primitive calls directly to `.prim`.
   Assemble support and translated bindings once, then feed the intended definitions to the reader and printer.
   Distinguish support calls from trusted primitive leaves. A helper-body mutation must reach the target evaluator and emitted OCaml.
   `Target.applyNamed` starts a helper with its parameters, not the caller environment.
   Model `max_int` as a profile dependency; `CompilerControls` currently supplies it only in its caller environment.
   Missing helper definitions, unknown dependencies, or failed reads must remain visible refusals.

4. `Ml.checkModule` alone cannot establish closed support definitions.
   Qualified names pass its value check. Raw expressions are opaque.
   A top-level raw prelude opens the value scope, disabling unbound-value reporting.
   Validate the restricted support subset separately, with explicit external dependencies and no raw escape.
   Check definition order or recursive groups, duplicate names, parameter arity, and collisions with primitive names.

## Table and application contract

Check uniqueness on normalized lookup keys, including `stripRedArg`, and preserve the clock-row priority.
Keep exact clock ingress, extern, carrier rewrite, constructor, and builtin dispatch in their current order.
Builtin arity counts relevant runtime arguments. Ordinary-call erased placeholders are a different rule.
Preserve operand permutations, labels, underapplication, and application of surplus arguments to the returned function.
The current source primitive interpreter refuses non-saturated calls before ordinary declaration application.
Use compiled Lean wrapper examples for partial applications, or establish a separate source-evaluator connector.
Do not treat that refusal as evidence that the new target result is wrong.

Derive lookup, reserved names, and the fidelity inventory from the table.
Retain an independent reached-name census so an omitted row cannot disappear from both the implementation and its test.
Every reached row needs an explicit domain and evidence or open status. Missing metadata must not default to exact agreement.
Keep the current arithmetic policy and row 108's open work visible.

## Small proof obligations

All following claims are proposed under `translation-simulation`, serving R8's typed-lowering open part.
They do not close M7 or prove the Lean or OCaml compiler.

| Proposed claim | Required property and consumer | Hypotheses | Observation | Exclusions | Immediate prerequisite |
| --- | --- | --- | --- | --- | --- |
| builtin-table-lookup | Lookup agrees with the normalized row enumeration; translator and fidelity report consume it. | Unique normalized keys, fixed alias and precedence rules. | Selected row or absence. | Meaning of the selected row. | Freeze the row data and normalization. |
| builtin-application-hygiene | Generated binders do not change operand denotations; `applyBuiltin` consumes it. | Admitted arguments, support closure, disjoint free names, relevant arity. | Result and modeled failure under the application contract. | Arbitrary host callbacks and source compilation. | State the fixed-reservation or fresh-allocation invariant. |
| builtin-support-agreement | A support call has the row's target meaning; conformance and emission consume it. | Related values, fixed target profile, resolved support dependencies, related budgets. | Result, modeled exception, or live fuel frontier. | Native performance and whole-runtime agreement. | Assemble the exact support definitions into the target evaluator. |
| builtin-inline-agreement | The admitted inline form agrees with its support specification; inline emission consumes it. | Substitution closure and the strictness, purity, and argument-domain conditions. | Named target outcome under related budgets. | Cost equality unless separately measured. | Decide the safe subset and its argument contract. |

Start with local lookup and hygiene facts, then one scalar support law.
Record open claims through the existing proof graph before proving them.
Keep Test/Conform dependencies out of the Effect4 core and Laws roots unless a separately reviewed module boundary permits them.
Shared syntax and successful type checking are evidence at their own boundaries, not semantic proofs.

## Landing order and documentation

```mermaid
flowchart LR
  A[Record row and application contracts] --> B[Table data and restricted support validation]
  B --> C[Shared support assembly and name checks]
  C --> D[Move translator and conformance consumers]
  D --> E[Capture and partial-application controls]
  E --> F[Regenerate and check actual OCaml artifacts]
  F --> G[Local proof and documentation receipts]
```

Keep the real-Lean capture reproducers and ordinary-name controls.
Include an asymmetric callback, erased arguments, aliases, partial applications, and a function-valued overapplication.
Add a bad support body, omitted support dependency, duplicate normalized row, and missing contract control.
Mutants must fail at their intended boundary. An unrelated compiler error is not that evidence.

Update `docs/core/lcnf-route.md`, `ocaml/README.md`, `docs/GENERATED.md`, and the affected module property lists.
Update the fidelity report description and the semantics registry without promoting open lowering or numeric claims.
Remove the separate copied fidelity table and handwritten reservation list only after their consumers use the new owner.
Preserve generated provenance and record the exact support/table inputs in freshness checks.
`check-gen` does not itself regenerate LCNF. Use the owning LCNF generation and OCaml acceptance route when the coordinator's lane permits it.
Check all four production outputs, including the engine prelude and functor assembly.
Respect active T3b/M0 ownership. No build or implementation dispatch comes from this review.

Keep performance claims separate. OCaml can optimize without Flambda, but an exact inlining claim requires evidence for the pinned build.
Prefer unchanged simple operator shapes for this slice. Measure any later helper-performance change on the emitted code.

Detailed source, proof, and primary-reference notes are retained beside this file.
