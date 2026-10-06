# FOCUS: a checked source view for Routing and nested loops

Status: research contract, not dispatched. Every declaration sketch is uncompiled.
No implementation takeover, repository change or project execution belongs to this packet.

Source cut: `c22f908def0c2a881ae46040d0dbaaaa57991352`.
Active staged Semaphore and report changes are excluded. `manifest.json` retains exact committed sources.
The earlier source cut is `4b57609c03ad0a38fd81cfc2c09ea5731dfe7ff0`.
Only `Program/Typing.lean` and `Laws/Program/ReferenceTyping.lean` change among the inspected focus owners between those cuts.
The change removes the redundant post-expansion emptiness check. This brief uses the new equation and retains reference validity.

## 1. The correction that makes this useful

Inspection is a typing capability, not a synchronous execution theorem.
The earlier report restricts its first checked view to `Looped`. That excludes its proposed Routing consumer.
Routing uses host operations and `catchIf`. Nested loops and Routing can nevertheless use the same checker-owned view.

The corrected domain is a supported source route in an admitted reference-free program.
Only the separate rewrite slice uses the `Looped` execution fragment.
Both earlier authoring documents now carry this correction and retain their prior versions.

The first consumer asks for the checked branch types at Routing's Boolean selection.
The second acceptance example selects the step of a nested `iterate`.
Neither consumer needs runtime frames, host execution, a new program representation or an editable expanded tree.

## 2. Exact first supported domain

The public input is an existing `Api.Built` and an address into its original stored program.
The program must satisfy `program.refSites [] = []` for this first view.
This is a restriction of the view, not an additional execution-admission requirement.
Programs containing references receive `referencesNeedOrigin` from this view and retain ordinary raw inspection and rebuilding.

An effect focus follows zero or more `Node.child` edges whose source and destination are both `.eff`.
It can stop at any effect node, including a `gen`, `withFiber` or `provideLayer` node.
It cannot cross from that effect into another source family.

| Parent | Supported effect child indices | Inherited environment |
| --- | --- | --- |
| `suspend`, `exit`, `uninterruptible`, `interruptible`, `scoped`, `restore` | 0 | `Γ` |
| `bind first rest` | 0, 1 | `Γ`; `Γ ++ [first.answer]` |
| `catchCause body handler` | 0, 1 | `Γ`; `Γ ++ [causeOf body.error]` |
| `catchIf test body handler` | 0, 1 | `Γ`; `Γ ++ [body.error]` |
| `select s d a0 a1` | 0, 1 | `Γ ++ (d.arms scrutineeTy).1`; corresponding second arm |
| `matchCause body onValue onCause` | 0, 1, 2 | `Γ`; `Γ ++ [body.answer]`; `Γ ++ [causeOf body.error]` |
| `onExit body finalizer` | 0, 1 | `Γ`; `Γ ++ [exitOf body.answer body.error]` |
| `acquireRelease acquire release` | 0, 1 | `Γ`; `Γ ++ [acquire.answer, exitOf unknown unknown]` |
| `iterate cursorTy initial test step result body` | 0 | `Γ ++ [cursorTy.getD initialType]` |
| `provideService key value body` | 0 | `Γ` |
| `provideLayer layer local body` | 1 | `Γ` |

Other nonempty routes either name no child or cross an unsupported family.
`gen` child 0 crosses to `.stmts`; `withFiber` child 0 crosses to `.action`; `provideLayer` child 0 crosses to `.layer`.
Return the stopped address and family as an opaque view refusal. Do not invent an environment or type beyond it.
A later return to an effect inside that family does not make the crossing supported.

This route domain contains every effect location in a reference-free `Looped` program, including nested loops.
It also contains Routing's effect routes. It does not require the whole program to be synchronous.
An unrelated unsupported family elsewhere in the program does not invalidate a supported route.
The existing checker still checks the entire input before yielding checked evidence.

### Ordinary term slots

At a supported effect focus, these direct fields are supported:

| Constructor | Named slots | Context before nested term descent |
| --- | --- | --- |
| `succeed`, `fail`, `sync`, `perform` | value, error, thunk, request respectively | `Γ`, constant mode false |
| `select` | scrutinee | `Γ`, false |
| `catchIf` | test | `Γ ++ [body.error]`, false |
| `iterate` | initial | `Γ`, false |
| `iterate` | test, result | `Γ ++ [cursor]`, false |
| `iterate` | step | `Γ ++ [cursor, body.answer]`, false |
| `awaitFiber` | fiber | `Γ`, false |
| `provideService` | value | `Γ`, false |
| `restore` | saved | `Γ`, false |

Nested terms use `TermRefusal`'s existing child convention:

- application arguments and record values use their list index;
- field and tuple projection target is zero;
- record update has target zero and replacement one;
- list fold has list zero, initial one and body two.

All current `Term` constructors are covered inside an ordinary term slot.
Variables and literals have no children. An unavailable index is an invalid address.
Application arguments use the atom's `constAtom` flag, ignoring the parent's mode.
Record values and record replacements use true. Projection targets use false.
A fold's list and initial use false; its body uses false under `Γ ++ [accumulator, item]`.
These are the existing `argTy` rules, not new inference choices.

Explicit first-slice exclusions:

- terms inside `CauseTerm` leaves;
- operation-carried binder terms, whose parameter type depends on row instantiation;
- type annotations themselves, including cursor and fold accumulator metadata;
- term slots inside generator statements, actions or layers.

The first two need distinct slot/refusal cases. They must not be silently treated as ordinary `Γ` terms.
The selected `failCause` or `perform` effect can still display its complete checked `EffTy`.
Raw syntax inspection remains available for excluded slots.

## 3. Data signature and owner

Reuse existing `Eff`, `Term`, `TyEnv`, `EffTy`, `Ty`, `EffFam` and `TypeRefusal`.
Add only query addresses, finite slot names, view results and view refusals.
These are derived views. No annotation is inserted into canonical program syntax.

Proposed notation, uncompiled:

```lean
namespace Effect4.Program.Checker

inductive FocusAddress where
  | effect (path : List Nat)
  | term (effectPath : List Nat) (slot : EffectTermSlot) (termPath : List Nat)

structure EffectFocus (Op : Type) where
  path : List Nat
  source : Eff Op
  env : TyEnv
  type : EffTy

structure TermFocus where
  effectPath : List Nat
  slot : EffectTermSlot
  termPath : List Nat
  source : Term
  env : TyEnv
  constant : Bool
  type : Ty

inductive FocusData (Op : Type) where
  | effect (view : EffectFocus Op)
  | term (view : TermFocus)
```

`EffectTermSlot` names the preceding table's slots. It does not duplicate the constructor tree.
`FocusRefusal` distinguishes missing address, unsupported family, unsupported slot and reference-origin requirements.
Preserve the existing located `TypeRefusal` if a raw checker input fails.
No new `Ty.unknown` fallback belongs in the view.

The checker companion takes `sig`, outer `Γ`, absolute blame prefix, source and relative query.
The public `Built.focus` fixes the signature and outer context from the built program.
A serialized client must resolve its document identity to that exact `Built`; this slice need not introduce a document store.

### Keep refusal of a view separate from refusal of typing

A useful combined function has this proposed result shape:

```lean
-- UNCOMPILED shape; final namespace and names remain reviewable.
checkWithFocus sig Γ base source address :
  Except TypeRefusal (EffTy × Except FocusRefusal (FocusData Op))
```

It first calls the existing `Checker.check`.
A valid program with an unsupported query retains the successful outer type and an inner view refusal.
Erasing the view therefore returns exactly the original checker result, including its refusal precedence.
An API facade over `Built` can eliminate or separately report the impossible raw-check failure using its law.
It must not reclassify an unsupported view as a program typing failure.

The query computation uses the generated program and term folds.
Its carrier may pair raw syntax with a query computation, as `TermRefusal.algebra` already does.
For sibling-dependent contexts, call the existing checker or term typer and reuse that result.
Do not reimplement answer joins, error residuals, normalized subtyping or row instantiation in the view.

The minimal first implementation can recompute a needed sibling check.
Caching can follow a measured consumer, with the full source/signature identity as its key.
Avoid refactoring the entire checker into a new instrumented acceptance engine for this slice.

### Inferred results and parent constraints are different

The first view reports inferred local results. It does not compute a universal expected `EffTy`.
The existing checker is not a bidirectional editor calculus. No Hazelnut theorem transfers to it automatically.

The branch and loop explanations expose named constraints from their actual parent rule:

- a Boolean select joins both inferred branch answers, errors and requirements; neither branch must equal that joined type;
- an iterate test must infer `bool`;
- an iterate initial value and step must infer types below the selected cursor type after normalization;
- an iterate body infers `⟨B,E,R⟩`; `B` becomes the step's answer binding, while `E` and `R` become the loop's columns;
- an iterate result infers the loop's answer `D`; this does not determine a unique expected `B`.

A step of type `nat` can be valid below a cursor type `nat | string`. Equality with the cursor type would reject it incorrectly.
A body-answer edit can leave the loop's final answer unchanged while altering the step's inherited context.
The view must renew that context rather than reusing a cached expected type.

Keep these two consumer-specific detail packets tied to `inv_select` and `inv_iterate`.
Do not introduce a general constraint language, a principal-type claim or minimal expected-type slicing in this slice.
A future expected-type capability needs its own rule, ambiguity policy and theorem.

## 4. Proposed statements and proof routes

All statements below are uncompiled sketches. Their helper relations describe checking evidence, not another acceptance judgment.
Every final theorem must retain the listed inputs and hypotheses.

### F1. View erasure

```lean
(checkWithFocus sig Γ base source address).map Prod.fst =
  Checker.check sig Γ base source
```

This holds for every source and address, including typing failures and unsupported queries.
It should follow from the wrapper definition and `Except` equations.
It is not a completeness theorem for the focus route.

### F2. Source and local-check soundness

For an effect focus:

```text
Checker.check sig Γ base root = ok rootTy
and focusEff sig Γ base root relativePath = ok view
imply
  Node.at_ (Node.eff root) relativePath = some (Node.eff view.source)
  and view.path = base ++ relativePath
  and Checker.check sig view.env view.path view.source = ok view.type
  and the inherited route from Γ to view.env is justified by the checker.
```

The last conjunct matters. A local check under an invented environment is insufficient.
Represent it as a proof-only path of successful checker descents, or prove the parent-to-child equations directly for each returned route.
It need not appear in the serialized view or become a generic category library.

Reuse `Checker.inv_bind`, `inv_catchIf`, `inv_select`, `inv_iterate` and the other existing arm inversions.
Use `Node.child`'s generated constructor equations for exact source selection.
The whole-path proof composes the one-step facts along the requested path.
A term query then uses the ordinary-slot rule and the existing `argTy` descent rules.

For a term focus, the concluding local equation is:

```text
argTy sig view.env view.constant view.source = some view.type
```

It also states exact selection by the containing effect slot and nested term path.
It must retain the inherited mode and environment, including list-fold binders.

### F3. Completeness and deterministic inherited context on the declared domain

```text
Checker.check sig Γ base root = ok rootTy
and the requested route stays in the supported domain
and its requested ordinary term slot and nested address exist, when applicable
imply there exists a returned checked focus at that address.
```

A route crossing an unsupported family is outside this theorem and produces its named refusal.
An absent address is outside it too. Neither case implies the source is ill-typed.

For fixed `sig`, `Γ`, `base`, `root` and address, successful results have equal environments, modes and types.
This follows from the computation's functional result and, for a relational route specification, checker-result uniqueness at each edge.
It does not assert that the selected subtree admits only one environment in isolation.
For example, a constant subtree can type under many unrelated environments.

### F4. Original-source public connector

```text
b : Api.Built
b.program.refSites [] = []
Built.focus b address = ok view
imply F2 with
  sig = (⟨b.table, []⟩ : SigApp).signature, Γ = [], base = [], root = b.program.
```

Reuse `b.admitted.toTypedProgram.typed`, `expandRefs_eq_self_of_refSites_nil` and `layerRefsWF_of_refSites_nil`.
Then unfold `typeOfProgram_eq_if_refsWF` and use the existing checker success projection.
This is the exact bridge from whole-program typing to the original source for this first slice.
It does not rely on the obsolete post-expansion emptiness test.

No original/expanded address transport is needed because the input is reference-free.
A program with valid references can have a typed expansion while a selected expanded path does not exist in original syntax.
Refuse that view now. Do not claim `TypedProgram.hasTy` supplies an origin map.

### Focused details used by consumers

The Routing branch detail follows from `Checker.inv_select` at the returned environment:

```text
scrutinee type t, d.arms t = some (Γ0, Γ1)
left type L under Γ ++ Γ0, right type R under Γ ++ Γ1
parent type = ⟨Ty.join L.answer R.answer,
               L.error.join R.error,
               L.requires.union R.requires⟩.
```

The loop detail follows from `Checker.inv_iterate`.
It retains initial type, selected cursor type, Boolean test, body type, step type, result type and both normalized-subtyping premises.
No runtime cursor is manufactured. Runtime membership and world extension remain separate.

## 5. Concrete Routing consumer

Use `Routing.routed false findByIdExact (named "NotFound") (named "Unauthorized") "secret" 2 "2"`.
This is the existing example whose exact error column reaches the target branch-printing issue.
Build it through the existing authoring entry point.

The source-derived candidate Boolean-select paths are:

- `[0,0,0,1]`: the token check inside `withAuth`;
- `[0,0,0,1,1,1]`: the permission check inside `getProfile`.

These paths follow the current authoring constructors. They are not newly executed observations.
The future fixture must pin the actual selected constructor after authoring; do not trust the written numbers alone.

The consumer exports or displays a branch explanation containing the selected syntax, inherited environment, both branch `EffTy` values and the actual join.
It must not use the whole request's final type as a proxy for a nested branch type.
The enclosing handlers alter the outer error column.
The exact row table also changes the local error column even when source structure is unchanged.

The follow-on printer can consume those checked branch facts at decisions row 218's `ifCase` seam.
Row 218 rejects an annotation on the printed arrow. Do not reopen that choice accidentally.
This focus slice does not change printer syntax or claim to fix the target's two reported errors by itself.
Target integration still owes the reader image laws and pinned compiler checks.

The loop fixture uses nested `iterate` with distinct cursor and body-answer values.
It selects all four pure slots and both levels' bodies.
A second version uses equal cursor and answer types, so swapping roles cannot hide behind a type mismatch.

## 6. Small edit fence and imports

Proposed source ownership:

| File | Work |
| --- | --- |
| `src/Effect4/Program/Typing/Focus.lean` | New finite address/view/refusal data and fold-based query; imports existing Checker and Fold |
| `src/Effect4/Api/Focus.lean` | New `Built.focus` facade; imports Built and the core view |
| `src/Effect4/Laws/Program/Typing/Focus.lean` | F1–F4 and helper consumers; imports CheckInversion, CheckedTyping and ReferenceTyping |
| `Test/Program/FocusContract.lean` | Nested-loop, ordinary-slot, mode, refusal and stale-context controls |
| `Test/Dogfood/Scenario/RoutingFocus.lean` | The exact Routing branch explanation consumer; imports existing Routing and the new facade |

No initial edit of `Checker.check`, `argTy`, `Eff`, `NodeLenses`, the printer or generated syntax is needed.
If a small checker-owned one-step helper removes duplication, propose its exact change before expanding the fence.
Do not move all checker rules or introduce a second annotated program carrier.

Coordinator import anchors:

- `src/Effect4.lean`: add the core view beside `Program.Checker`, and the facade after `Api.Author`;
- `src/Effect4/Laws.lean`: add the law module beside `Typing.CheckInversion`;
- `Test/All.lean`: add `FocusContract` beside checker controls, and `RoutingFocus` after Routing.

`Api.Built` imports `Api`. Therefore `Api.lean` cannot import a facade that imports Built.
Use the existing companion-module pattern and the `Effect4` library root.
The namespace can remain `Effect4.Api` without introducing that cycle.

The registry, decisions, roots, generated manifests and axiom gate remain coordinator-owned.
A new serialized boundary is not necessary for this slice. Do not add codecs without its consumer.

## 7. Five-part placement

1. Concept: `residual-program-typing`. Required property: the displayed local checking judgment follows from the exact root check and its inherited route.
2. Question and role: proposed claim `checked-focus-context`, compatibility/inversion. F1–F4 are its proof decomposition. Existing `rebuild-admission` consumes future edits; Routing's branch explanation consumes F2 and F3 immediately.
3. Reach: fixed signature, outer context and original source; public input is admitted under `⟨table, []⟩`; reference-free source; the exact route and slot domain above.
4. Nonclaims: no principal runtime frame type, runtime value membership, capture transport, behavior preservation, minimal error slice, target typing, host agreement, progress or termination.
5. Unlock: serves R1 through exact signatures, R8 through a checked source view for a face, and R10 through the existing branch-printing consumer. It supplies a future source fact for M5; it does not strengthen M5–M7 itself.

The helper selecting a term slot serves the same claim and consumers. It needs no separate top-level theory claim.
The new role is a derived typing view. It is not another judgment among formation, membership, codec and reply admission.

## 8. Adversarial acceptance cases

- Same node bytes and address under two row tables produce different inherited contexts. A cache keyed only by source is refused.
- Replacing a bind's first effect changes the untouched continuation's context. Reinspect it under the new document.
- A constant subtree has more than one possible isolated environment. Only the root-derived one is displayed.
- An application changes its children's constant mode. A record value and a record target use different modes.
- A nested list-fold body adds two bindings inside a loop step. Neither set of bindings may overwrite the other.
- A nested `iterate` distinguishes outer inputs, inner cursor and inner body answer, including equal-typed values.
- The four loop term slots share the effect path but remain separate addresses.
- A valid reference expands to children absent at the original reference site. The first view refuses instead of returning a falsely editable path.
- A valid route to a `gen` node succeeds there; attempting to cross into its statements yields only `unsupportedFamily`.
- Routing's host and `catchIf` nodes remain inspectable despite failing the `Looped` predicate.
- An unsupported view does not change a successful checker result. A failed root check keeps its exact original refusal.
- A reported Boolean-select type joins both branches' answer, error and requirements, not just its final answer.
- A narrower step type under a wider cursor is accepted; a non-Boolean test and a step outside the cursor type are refused.
- Equal overall loop result types do not determine a unique expected body-answer type.

`probe.py` retains isolated finite models of the risky cases with positive controls.
They are not Lean counterexamples or compiled Routing executions.

## 9. Future verification and stop rules

No command in this section has run in this research task.
After authorization, first elaborate the passive carriers and statement skeletons at the pinned Lean version.
State `proof_goal` obligations with placement before proving them. Do not replace unavailable statements with `True`.

The narrow build should cover the new core, facade, law module and both fixtures.
Query each top theorem's axioms and plan status. Retain the exact output.
Use the existing module and traversal rules; generated folds should prevent a new hand traversal exemption.
If the chosen API requires a handwritten policy match, run the reached case census at implementation time.

Stop and report a contract conflict if a supported route needs a stronger signature premise or an unlisted context state.
Do not drop Routing or nested loops to make a proof easier.
Do not silently treat a reference-expanded path as an original source address.
Do not claim compiler or host acceptance from the source focus fixture.

Finishing criteria: Routing branch context and nested-loop slot context use one API; F1–F4 are proved within the existing axiom ceiling; all declared refusal controls pass; the public import closure stays acyclic.
