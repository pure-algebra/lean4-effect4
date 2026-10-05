# Builtin data refactor: source review

Accept the direction. Land the data table with explicit application and name contracts, before semantic or performance substitutions.

Evidence status: source inspection at `182312f30194f0beefa7a6273eb1144aa834c0f0`.
The worktree is unchanged. The new design is supplied by the coordinator; no tracked builtin-table plan appeared in the focused search.
This note incorporates the parent review of UI70: inline forms are binder-free and linear, and support functions use `Ml.Bind`.
Inline parameters occur at most once; zero occurrences are allowed. Eta names may use a computed reserved range.
No build, generator, installation, repository edit, or new runtime probe ran.

## 1. Preserve the application contract

`Translate.argExpr?` drops erased and type arguments for builtins and extern rows. Ordinary calls keep `unit` placeholders through `argExpr`.
`wrapperKeep?` and `wrapperParams?` reconstruct the wrapper's missing arguments before calling its reduced-arity twin.
A table's arity must mean relevant runtime arity. It is not the original Lean declaration's parameter count.

Keep the existing dispatch order: exact clock ingress, extern row, carrier rewrite, constructor, builtin, ordinary translated call.
`Clock.builtin?` currently has precedence within `builtin?`. A generic table must preserve clock ownership and its exact carrier.

Check unique normalized keys after `stripRedArg`, including clock rows. Unique raw Lean names are insufficient.
Intentional aliases must identify one row. Conflicting normalized entries must refuse visibly, rather than win by list order.

A target tag `op/fn/identity` alone does not describe argument arrangement.
`List.all` and `List.any` reverse their two arguments. `List.contains` and `List.elem` have different relevant argument orders.
`Option.getD` supplies a labelled default. `Array.get!` includes its relevant default argument.
Represent those arrangements as data, or keep them in named support functions with source-order parameters.

Overapplication is real. A builtin can return a function, as `Prod.fst` or an identity conversion can.
Apply the first arity arguments to the row, then apply the remainder to its result, preserving their order.
Do not reject every call above the row's arity or send the remainder into the row's argument permutation.

## 2. Hygiene must also preserve evaluation

`Translate.argAsList` can insert a `to_list` carrier conversion. Consequently, translated builtin arguments are not always variables.
The conversion can allocate and its cost is already reported by `useAsList`.

For an underapplication, evaluating provided arguments inside the new lambda can delay them or repeat them on each call.
Do not prescribe hoisting without the intended observation. Choose one explicit sequencing contract.
Either preserve the required evaluation with outer let bindings, or admit only total pure conversions under an observation excluding allocation and cost.
The second choice must identify the permitted conversions and their assumptions. It does not cover foreign effects, exceptions, or nontermination.
An atomic-argument entry-point restriction is another sufficient choice, if checked.

Binder-free linear inline forms reduce substitution risks. They do not alone establish evaluation preservation.
An unused parameter can discard a supplied conversion; a parameter in an untaken conditional branch can defer it.
At-most-once occurrence is not an exactly-once evaluation guarantee. The same totality/purity or sequencing contract must cover these cases.
Keep existing LCNF lets intact and test callback observations, exceptions, and calls repeated through one returned function.

OCaml does not specify application-argument evaluation order. Use explicit lets whenever an observation needs an order.
Source: [OCaml 5.1 reference manual, expressions](https://ocaml.org/manual/5.1/ocaml-5.1-refman.pdf).

The same hygiene policy must cover `ExternFn.apply`, whose current binders are `_ex1`, `_ex2`, and so on.
The `_redArg` route already obtains `_eta` binders through `fresh`; preserve that route's parameter filtering.
A single application constructor can be shared after each route has decided its own argument layout.

The selected computed reservation of `_b1` through the table's maximum arity is acceptable. Fresh spelling at every site is not required.
Its contract must ensure that these names are disjoint from the free variables of every supplied expression.
Include carrier conversions, extern literal dependencies, and every expansion entry point. Internal support binders need their own closed scope check.
An assertion that arguments are not nested expressions is insufficient: `argAsList` can introduce an application.
A nested expression is safe when its free variables satisfy the contract; an unreserved variable is unsafe even without nesting.

## 3. A collision check needs the whole emitted scope

Derive reserved free names from builtin rows and their support definitions.
Include normal translated global names, primitive prelude names, extern heads, and extern literal leading arguments.
Qualified heads need their module roots protected if a future form admits local modules.
Do not reserve only the table's helper names.

`Translate.emissionGroups` currently checks duplicate names and computes dependencies only for translated declarations.
`primitivePrelude` is prepended afterwards. The engine's raw prelude is inserted separately by `LcnfGen`.
Named support definitions need one dependency-closed assembly with deterministic ordering and duplicate checks across those boundaries.
Permit recursion through explicit dependency groups, or reject it in the first support profile.

`Ml.checkModule` does not establish that a reference reaches the intended declaration.
It checks unqualified name membership. Qualified references are trusted; raw bodies are opaque.
Raw declarations or open/include also relax the unbound-name check. All top-level names are collected before bodies are checked.
Thus it does not replace capture checks, sequential dependency ordering, or checking raw-prelude exports.

Freshen generated source locals against the complete reserved set. Computed reserved eta names can then be reused under the stated disjointness contract.
Use a final validator to catch missed cases.
A blanket refusal of every harmless local/global name overlap would narrow the accepted source profile unnecessarily.
The final validator should detect ambiguity in the emitted references, with a named and located refusal.

## 4. Share support syntax without overstating its meaning

A named support function represented by `Ml.Expr` removes duplicate helper bodies from call sites.
Validate its binder scope separately under a closed, explicit set of support/library dependencies.
Do not inherit the enclosing raw-prelude module's open-scope exemption for this check.
That is useful even before an evaluator exists.

`Ml.Syntax` explicitly owns untyped surface syntax. `Ml.Check` leaves target typing to OCaml.
A shared evaluator and renderer remove one duplication, but neither proves that OCaml runs the evaluator's semantics.
Use the smallest supported pure fragment. Unsupported expression forms and unknown primitive names must refuse visibly.
Short-circuit operators require short-circuit evaluator rules. Do not evaluate both operands eagerly through a generic primitive list.
Keep exceptions and out-of-domain results distinct from ordinary values and from bounded evaluation exhaustion.

The table's fidelity/domain fields should distinguish exact, bounded, deliberately different, and unsupported rows.
Notes alone do not enforce a domain. Current natural saturation and the narrow UInt64 carrier do not meet arbitrary-precision Lean arithmetic.
Preserve those current boundaries during the structural refactor; row108 remains open.

No generic-comparison speedup or helper count is established by this review.
Table lookup happens during generation; moving a generator match into data does not itself speed the emitted program.
Measure target changes separately with the pinned compiler, flags, actual emitted bytes, and a representative consumer.

## 5. Smallest landing order

1. Inventory rows, normalized aliases, runtime arities, argument layouts, current domain cuts, and free dependencies.
2. Add checked row data, binder-free linear inline forms, and checked support syntax beside the existing lowering. Preserve the current result and refusal policy.
3. Move builtin and extern underapplication to hygienic application construction. Check the reserved-name disjointness and the selected sequencing premises.
   Keep route-specific erasure and wrapper reconstruction.
4. Assemble support declarations and ordinary declarations with complete names and dependency checks. Migrate both target consumers.
5. Regenerate and review the exact artifact set; then run the existing focused checks and compiler/runtime controls under seat ownership.
6. Consider semantic and performance substitutions individually, with a measured consumer and their own relation.

The four persistent artifacts are named by `ocaml/gen/roots.json`: `fibers_gen.ml`, `machine_gen.ml`, `api_gen.ml`, and `engine/api_engine.ml`.
Their producer is `scripts/generate.py` through `OCaml5.Tools.LcnfGen`; closure manifests and the extern usage ledger remain consumers.
Add the new module to generation/freshness inputs and document references. Ordinary `check-gen` does not regenerate LCNF.
Use the existing OCaml CI path and `check-gen-full` when their owned validation slice calls for regeneration.
The separate conformance evaluator consumer must receive the same support assembly, without pretending its current fragment covers full Ml.

## Proposed proof placement and controls

Concept: `translation-simulation`. Requirement: R8, its open typed-lowering part. These are proposed obligations, not Lean-checked proofs.

- Application construction preserves the declared argument observation under a valid row and reserved-name disjointness.
  Its sequencing premise is explicit: atom/let-binding preservation, or admitted total pure conversion with allocation and cost excluded.
  Consumer: builtin/extern expansion. Observation: returned value, permitted failure, callback trace, and captured arguments on repeated application.
  Excludes whole-LCNF correctness and arbitrary foreign effects. Prerequisite: validated runtime arity and argument-layout data.
- Support closure contains each required definition once, orders dependencies, and preserves each reference's intended binder.
  Consumer: `LcnfGen` and the conformance assembly. Observation: resolved references and emitted dependency groups.
  Excludes OCaml compiler correctness. Prerequisite: explicit support dependencies and prelude/export accounting.
- Scalar support evaluation agrees with its emitted function on the named numeric domain.
  Consumer: conformance controls and a later R8 scalar relation. Observe values, failures, and short-circuit behavior separately.
  Excludes row108's unresolved wider numeric profile. Prerequisite: actual shared syntax and a declared evaluator fragment.

Retain positive controls beside mutants for: normalized duplicate keys, wrong erasure count, swapped arguments, zero/full/partial/overapplication,
name capture, repeated or discarded conversion, conditional conversion, a missing transitive helper, wrong dependency order, short-circuit exceptions, and numeric boundaries.
Source-constructed expression controls are not evidence that persisted LCNF reaches each shape. Include both evidence kinds where available.
