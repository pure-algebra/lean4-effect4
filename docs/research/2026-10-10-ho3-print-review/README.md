# HO-3 review: callback requirements, names, and service boundaries

Before widening HO-3 acceptance, carry callback requirements into the printed TypeScript result.
Close the name-capture cases and refuse deferred service forms explicitly.
These are findings about the proposed design and working changes, not regressions in shipped HO-3 support.

[The generated-output follow-up](followup-1945/README.md) adds a shared annotation finding and completes the reconstruction audit.

## Scope and evidence

The landed base is `54ed060e6f12ebad49c05acd791a75e4425bd2f9`.
The owner works on `claude/ho3` from `41151468ffd97d0df25ed7d13080eee783ab199e`.
[The placement](PLAN.md) names the concepts, consumers, reach, limits, and requirements before the probes.
[The proof outline](PROOF-DAG.md) assigns the remaining work to existing claims.

The review reads a bounded recent session tail and verifies the repository working directory.
Claude reports the shared spelling laws built and is repairing the module round trip.
No message was sent to Claude, and no owner file was changed.

The probes use the owner's compiled imports from the isolated review worktree.
They do not rebuild those imports from source.
The source and artifact hashes stay unchanged during each recorded run.
[The results](checked-results.json) record the callback checks and target checks.
[The corrected naming fixture](checked-results-followup.json) records its successful narrow run.
[The audit](checked-results-audit.json) records the shared spelling module's dependency check.

The TypeScript samples are handwritten projections of the proposed headers and existing call sites.
They are not generated compiler output.
The initial local import path used older review artifacts; `results.json` retains that failed setup attempt.
The rerun uses the owner's imports and checks the four-child definition block.
The naming fixture also corrects its row-kind spelling, field-list type, and expression comparison before its successful run.

## HO3-REQ-01: a callback can require a service

`ParamDecl.admits` in `src/Effect4/Program/Checker.lean` checks the answer and error columns.
It does not require an empty service row.
The invocation checker adds every argument program's requirements to the definition's requirements.
This lets an enclosing service provider satisfy a callback's needs.

The draft `paramType` in `src/Effect4/Codegen/Print.lean` instead emits this header:

```typescript
const consume = (
  a0: number,
  use: (a0: number) => Effect.Effect<number, never, never>
): Effect.Effect<number, never, never> => Effect.suspend(() => use(a0))
```

[Requirements.lean](Requirements.lean) checks a callback that reads service `k4_4`.
Its open invocation requires that service.
Providing the service around the invocation yields a checked closed program and a machine result of `7`.
A pure callback yields `1`; providing the service inside the callback yields `7`.
A callback with the wrong answer type is refused.

Pinned tsgo `7.0.0-dev.20260629.1` rejects the externally provided callback under the planned header.
Its diagnostic says the service requirement cannot fit `never`.
The pure and internally provided callbacks pass and execute against Effect `4.0.0-rc.112`.

The smallest useful target interface infers one requirement variable per callback:

```typescript
const consume = <R>(
  a0: number,
  use: (a0: number) => Effect.Effect<number, never, R>
): Effect.Effect<number, never, R> => Effect.suspend(() => use(a0))
```

[The candidate](candidate-positive.ts) passes tsgo and returns `[1, 7, 7]` for those three cases.
[The negative control](candidate-negative.ts) still fails when execution lacks the required service.
No cast, `any`, or erased requirement is needed.

For several parameters, infer `R0` through `Rn` and union them with the declaration's own requirements.
Authors keep their current parameter declarations and callbacks.
They should not repeat the callback's service row in another stored field.
`ParamDecl` need not gain a requirement field for this repair.

The current TypeScript syntax carrier has no type-parameter binder on `Expr.lambda` or `TypeRef.function`.
Its `Expr.generic` represents type application, not a binder.
A structured target binder and its renderer, reader, binding analysis, and generated images therefore precede this candidate.
Never encode the binder in an identifier string.
This target requirement variable is separate from HO-4's generic source types.

If that target extension cannot fit HO-3, retain a located target-profile refusal for nonempty callback requirements.
Keep the Lean checker unchanged and state the narrower printing profile.
That interim refusal must inspect each actual callback; declaration parameters alone do not contain its requirement row.

## HO3-NAME-01: whole row names do not describe lexical uses

The draft `paramsNameFault` compares a parameter with each row's entire spelling.
A parameter named `Widget` therefore passes beside a row spelled `Widget.run`.
A parameter named `Token` passes beside a row whose trailing argument names `Token`.
A parameter named `Payload` also passes when the body constructs the generated class `Payload`.

[NamesAndServices.lean](NamesAndServices.lean) copies the draft predicate into the probe namespace.
It checks those acceptances and confirms that the payload module passes the existing class collector.
It also checks existing refusals for `a0` and duplicated parameter names.
[name-capture.mjs](name-capture.mjs) compares each collision with an unshadowed callback name.
The qualified call and constructor fail with `TypeError`; the trailing argument silently becomes the callback itself.
The unshadowed controls return their intended values.
These are lexical controls, not execution receipts for generated modules.

Reuse `SourceBindings.qualifiedRoot` and `RowArg.names` for row references.
Combine those names with the payload classes the body references.
Do not introduce another independent list of imported names or helpers.
`exportNameSafe` already covers those names and generated value binders.

The immediate conservative check can use the module's relevant row roots, trailing names, and class names.
A later precise check can index those same uses by lexical scope.
`SourceBindings` already records a use with its environment; reuse that distinction.
Its value/type availability check alone does not distinguish a captured function from the intended external object.

A structural print/read theorem can succeed even when JavaScript resolves a name to the wrong binding.
Keep target binding checks separate from the reconstruction theorem.
Service-name equality alone is not an observed defect: the current key printer builds service keys structurally.

## HO3-SVC-01: deferred service callbacks need a refusal

HO-5 owns callbacks on service methods, but the new `printDef` handles parameters for every definition role.
`serviceFaultOf` does not exclude parameters on service initializers or methods.
`methodClosure` supplies only the request; `printService` supplies no callback to the initializer.

The Lean controls confirm both service shapes pass the current service hook.
They also inspect the method closure's actual one-argument call.
[The target control](service-negative.ts) yields two tsgo argument-count errors against the planned headers.
The ordinary service and a parameter-bearing plain helper remain positive controls.

Until HO-5 implements forwarding, refuse parameter-bearing `serviceInit` and `serviceMethod` roles at the existing service hook.
Identify the declaration and the deferred feature in the refusal.
Do not make every plain definition wait for HO-5.
This is enforcing the chosen slice boundary, not requesting HO-5 early.

## Useful consolidation already in progress

Claude now shares `LawfulSpelling.extend` between definition rows and parameter rows.
`NamedRows`, `LawfulIndex`, and `RowsNamed` describe the common extension once.
`LawfulSpelling.withDefs` and `LawfulSpelling.withParams` consume that law.
This reduces duplicate proof work while retaining their distinct scope premises.

The independent cycle-aware audit checks 166 declarations in `Effect4.Laws.Codegen.Definitions`.
They stay within `[propext, Quot.sound]`, with zero planned goals and zero declarations resting on goals.
The audit covers the compiled working module, not the unfinished HO-3 landing or its runtime behaviour.

Claude also starts pairing declaration/body entries in `readDefs_printDefs`.
Each body uses its own `withParams` signature and `paramsSpell` map.
Do not build a parallel context framework for this work.
Finish the existing route through `blockReadable`, G6, and the API consumers.

## Landing order and live authoring

1. Close the target-profile, lexical-name, and deferred-service refusals before widening acceptance.
2. Finish the existing per-definition reader and shared spelling laws.
3. Add invocation printing and reading with caller-context controls.
4. Run narrow law builds, cycle-aware audits, and the reached target, reader, and truth gates.

Keep formation, source typing, target support, reconstruction, and execution as distinct tool results.
A service-using callback is well typed even when the current target profile cannot print it.
The editor can display that callback's inferred requirement and its nearest provider.
A name refusal can identify the parameter and the captured row root, trailing name, or class.
A service refusal can identify HO-5 without changing the source typing judgment.

Cache body analysis by the body plus its declaration's parameter context, row table, and class inventory.
Changing those inputs must invalidate the associated diagnostics and reconstruction certificate.
A certificate for one parameter context does not justify reuse under another context.
This is a proposed cache condition, not a cache correctness theorem.

## Checks and limits

The successful finite runs contain 27 Lean guards across the two probe files.
The target checks use tsgo `7.0.0-dev.20260629.1`; runtime controls use Bun `1.4.2` and Effect `4.0.0-rc.112`.
Each negative target control fails for the intended requirement or argument-count reason.
No full sweep, merge, push, production edit, or new proof obligation occurs.

```sh
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-ho3-print-review/run_probes.py
```

The command expects this review worktree and the named owner worktree's compiled imports.
The recorded commands and input hashes define the evidence boundary.
Rebuild the narrow owner modules before using a new source revision as fresh proof evidence.
