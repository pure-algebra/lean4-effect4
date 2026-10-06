# Dogfood: type and authoring friction

## Answer

The reviewed commit is `00b160d25d6929ab7ba3aa19cc00fa6fdcfa9674`, clean at the opening snapshot.
This is a source review. It runs no Lean, compiler, runtime, build, generator, or installation.
The 29 source snapshots are retained in `source-manifest.json`.
The current Pool integration evidence is separately retained in `heartbeats/2026-10-06T140639Z/pool/`.

The examples do not establish a need to replace the type model.
They expose three concrete API improvements and one narrower proof-domain gap.
The larger missing service examples concern retained behavior, already reserved by row 234.

## 1. Use the hygienic callbacks at the actual callers

**Witnessed friction.** `Workers.note`, `Atomic.note`, and `Timeout.note` are byte-identical definitions.
Each accepts an arbitrary caller term `x`, then embeds it below the fixed name `xs`:

```lean
def note (log x : TermSrc) : Src NativeOp :=
  Ref.update "xs" (app "append" [var "xs", app "cons" [x, app "nil" []]]) log
```

They live in `Test/Dogfood/Scenario/{Workers,Atomic,Timeout}.lean`.
`source-controls.json` confirms the three identical bodies without executing Lean.
The current closed scenarios do not establish a capture failure.
The reusable helper's fixed binder can nevertheless capture an ordinary caller variable of that name.

**Small recommendation.** Migrate these callers to the already generated `Ref.updateWith`, then share the helper in the existing scenario support.
Do the same when touching generic builders that embed arguments below fixed `selectOption` or `onExit` names.
The existing `selectOptionWith` and `onExitWith` already supply those forms.
No new syntax, type constructor, or macro framework is needed.

Proposed sketch:

```lean
Ref.updateWith log fun xs => app "append" [xs, app "cons" [x, app "nil" []]]
```

**Property and placement.** Preserve each admitted caller variable's binding while elaborating a binder term.
Use `performTermWith` in `Program/Authoring.lean`, generated wrappers in `Authoring/Rows.lean`, and `var_push_minted` in `Laws/Program/Author.lean`.
This serves `operation-data-scoped` under `initial-algebras-folds`, and the consumers' R4/R10 typing and term-reading connectors.
The premises distinguish ordinary nonreserved variable readers from arbitrary scope-inspecting `TermSrc` functions.
Scope hygiene alone proves neither typing nor evaluation equality for every such function.

**Proposed control, unrun here.** Give outer `xs` the list `[7,8]`, and the log `[100]`.
Append `length (var "xs")`: the intended result is `[100,2]`; a captured log binder gives `[100,1]`.
The types coincide, so this control tests meaning rather than merely rejection.
Pair it with a noncolliding variable and the existing scenario observations.
The prerequisite is the existing callback API, already landed.

## 2. Give typed initialization one reusable home

**Witnessed friction.** Workers, Atomic, and Timeout import `P3WorkerQueue.ascribe` solely for their typed empty log cells.
The helper uses the existing record declaration and field read:

```lean
def ascribe (ty : Ty) (e : TermSrc) : TermSrc :=
  field (record [("v", false, ty)] [("v", e)]) "v"
```

`P3WorkerQueue.logAppend` records why it is needed: bare `Ref.make([])` fixes the invariant cell at `Ref<never[]>`.
Its first string append is refused. `logAscribed` builds, returns its two lines, prints, and reads back in the retained guards.
The invariant reference rule is doing its job. Loosening reference variance would hide the error.

**Small recommendation.** Extract this ordinary helper into the existing authoring utilities when these callers next move.
Retain its record-based implementation and existing printed shape.
Give it local typing and reading lemmas through existing record rules.
It is useful before the separately planned operation-carried `Ref.make<A>` slice.
It must not be described as that feature already landing.

**Exact connector shape, proposed and uncompiled here.**
At a scope, let `e` type as `S` under the record's constant flag.
Assume canonical `T`, a formed one-field declaration at `T`, and the record's accepted subtype check from `S` to `T`.
Then the helper has type `T` under either outer flag.
If `e` reads value `v`, the helper reads the same `v` through `reads_record` and `reads_field`.
The typing proof uses `types_record`, `types_field`, and the existing `Record.check` relation.
The consumer is log initialization and later Queue/Pool public initialization.
Place typing under `store-typing`, R4, and reading as a helper of the existing module-expansion claim, R10.
Exclude unchecked casts, arbitrary type assertions, target allocation/cost, and full admission.

**Controls.** Retain the accepted typed empty list and rejected wrong-element append.
Add an accepted string widening through a declared string field, plus a wrong declared type refusal.
Do not widen a string tag implicitly at every construction.
The immediate prerequisite is an agreed helper home, not a new language decision.

## 3. Make the intended error domain explicit in application rows

**Witnessed learning.** Routing's ordinary repository row accepts `(string,string)` failures.
Its `business-tag` run receives `("NotFound","db")` from that row and answers HTTP 404.
The handler cannot recover the sender's intended category from a broad pair type.
`Routing.findByIdExact` instead declares the existing union of `SqlError` and `SchemaError` tagged pairs.
The Lean `exact-business-tag` control refuses the same reply; its `exact-escape` control passes the infrastructure failure through.
These are Lean scenario controls, not successful execution of the printed exact-error program.
`Keyed.keptOut` excludes `routing/exact-escape`: retained tsgo 7.0.0-dev.20260629.1 reports two `TS2375` diagnostics.
The existing plain-routing host success does not cover this exact-error twin.
These controls are in `Scenario/Routing.lean` and need no new error representation.

**Small recommendation.** Use the exact row as the positive application-contract example.
Keep the broad row as its deliberate negative control, preserving the old example's stated fragment.
Build a focused handler composition around the exact row before widening the example into a service implementation.
Do not silently narrow unrelated adapters that intentionally expose broader errors.

**Property and placement.** On this declared row, an admitted failure inhabits its tagged union.
The handler then preserves failures outside the two named business tags.
The first obligation belongs to existing reply admission, R6, under the actual row signature and codec premises.
The second serves the already placed `infrastructure_escapes` goal, with the scenario's stated program and script domain.
The observation is the full escaped failure and absence of a business response.
It does not establish semantic provenance of arbitrary strings, trust in a host, or all future handler compositions.
Prerequisite: retain the exact row and its Lean positive/refusal controls.
Before promoting it to the target-facing application example, resolve the conditional printing inference refusal and rerun its named target check.

## A concrete remaining target type connection

The exact Routing twin exposes a target inference gap, separate from the ratified literal policy.
`Templates.effRows` prints a Boolean select as `Effect.suspend(() => condition ? left : right)`.
The pinned `Effect.suspend` asks for one callback result `Effect<A,E,R>`.
The retained diagnostic infers `E = readonly ["Unauthorized", "bad token"]` from one branch.
The other branch also contains `NotFound`, `SqlError`, `SchemaError`, and another Unauthorized payload.
Its union cannot fit that narrower inferred error type. A second nested select has the same problem.
The compact exact saved diagnostic is `routing-supplement/diagnostic.json`; no compiler runs here.

The Lean checker already joins both branch answers and errors and unions their requirements.
`HasTy.select` states that same rule and explicitly records the single-branch requirements rule as a red control.
The target gap therefore does not justify erasing tags or broadening the application's source error domain.

**Narrow candidate, uncompiled.** Carry the checked local joined `EffTy` to Boolean-select emission.
At that site, supply the represented answer, error, and requirement types to the suspended callback or explicit call arguments.
Reuse `declarationType`, `requirementType`, and the existing supported type/class projection.
The current raw printer receives a signature and environment length, not the local type environment or child typing derivations.
A constant template edit cannot safely invent these branch types; the checked emission path must supply the missing information.
The reader must recognize the chosen annotated image and check its annotation, preserving exact print/read laws.

**Property and placement.** This serves the existing typed target connection under `translation-simulation`, R8.
Its immediate consumer is the exact Routing printed module, with both nested Boolean selects.
Assume source branch typing at the actual local environment, representable joined columns, supported classes, and the pinned target profile.
The observation is target type acceptance with the full joined answer/error/requirements and reconstruction of the same source program.
The control set retains exact-routing acceptance, wrong branch-column refusal, and a branch with a distinct service requirement.
It excludes a general TypeScript preservation theorem, runtime agreement, inference for arbitrary external TypeScript, and silent widening of string tags.
The prerequisite is a design for transporting the already checked branch types through emission and the corresponding reader image.
Neither the candidate nor its controls has been compiled by this scout.

## The narrower proof-domain question

`TypesEach` in `Laws/Modules/Checking.lean` asks for one type under both literal flags.
`Kept` in `Laws/Modules/Waiting.lean` retains that typing through reachable minted scopes.
This makes general module proofs reusable, but a bare string literal has different types under the flags.

The gap is witnessed without a type-system failure.
`Test/Program/PoolSteps.lean` accepts `Pool.initial .string [str "x"]`, while `initial_types` does not cover that caller premise.
`Queue.offer_types` similarly requires a `Kept` message and explicitly excludes bare string literals from that theorem's domain.
The whole application checker may still accept them.

Prefer a small transport/ascription lemma at the actual occurrence over changing frozen theorem statements or erasing literal tags.
A later generalized theorem may track the occurrence's flag and subtype relation explicitly, if a consumer needs it.
That is a proof-interface decision, not evidence that `Ty` needs replacing.
`Captured` and `CapturedTy` also remain distinct: keeping a type does not show that a term keeps its value.

## What is already fixed

- `Api.Author.build` already returns `Api.Built` with the exact table, program, and admission certificate.
  `Built.typed` projects the retained typing; `Built.rebuild` fully readmits an edited candidate.
  Add no parallel certificate wrapper or checker.
- Arbitrary typed state and atomic `Ref.modify` already support different answer and stored types.
  Atomic's decision and deposit use one update each. The racy variant is a deliberate semantic control.
- `Scenario/Faces.lean` now records print/read success for all four scenario programs.
  Binder terms, Deferred type arguments, and Timeout's stated cursor are no longer those earlier blockers.
- The generated `pair`/`tuple` helpers now widen immediate number and Boolean slots while retaining string tags.
  Records, lists, nested supplied tuples, and invariant handles remain untouched.
  This is the ratified target profile, not arbitrary TypeScript refinement preservation or a general R8 proof.

## Deeper compositional consumers still missing

Workers' `Jobs.take` remains a host row. It does not yet exercise the newly landed Queue composite.
Routing threads CurrentUser as data and calls host rows; it does not encode the original layered service graph.
P5's listeners, captured service methods, and cancellation effects require retained behavior, which row 234 reserves.
Do not infer those missing programs from success of their current fragments.

The type model already represents the values used by these fragments.
The next theory work is the actual connector: captured behavior and lifetime, exact host reply boundaries, and stateful wrapper laws.
None follows solely from an admitted program, a typed helper, a finite script, or an unchanged print/read round trip.
