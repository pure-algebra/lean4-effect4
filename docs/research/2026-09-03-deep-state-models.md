# Deep state models: Ref, Deferred, Layer, and Scope's six partial rows

Research note, 2026-09-03. Head `6d83533`. Pin `effect@4.0.0-rc.112`,
upstream `2600f62f4532026928454dcea8d1c48557b3f942`
(`generated/effect-runtime-census.tsv:4`).

## Summary

1. The census carries 137 mechanism rows; 117 are in the denominator; 43 are `absent`. 38 of those 43 are `ref.*` (10), `deferred.*` (12), `layer.*` (16); the other 5 are `op.Yield`, `op.Async`, `checkpoint.runloop-top`, `checkpoint.post-yield-cancel`, `rule.yield-is-overloaded` — the park/resume rows (`Effect4Test/Audit/RuntimeCoverage.lean:2604`, `:2605`, `:2723`, `:2733`, `:3291`).
2. Those 5 are the *only* hard blocker: `deferred.await`'s resume half is `internalEffect.callback`, i.e. `op.Async` (`vendor/effect-4.0.0-rc.112/src/Deferred.ts:173-186`, `internal/effect.ts:1163-1169`). Everything else in the three families is a first-order store transition.
3. Ref is a heap `List α` plus a key; nine of ten rows are one-step equations over it. Only `ref.make`'s "distinct cell per evaluation" needs a freshness discipline, and that is the `SCOPE-FB-KEY-IDENTITY` shape already used in `Effect4/Runtime/Scope.lean:318`.
4. The Ref answer alphabet must have a `cell` arm. `Ref.set` succeeds with the `MutableRef` (`Ref.ts:307`, `MutableRef.ts:1063-1070`) while `Ref.update` succeeds with `undefined` (`Ref.ts:1273-1276`). Two `void`-declared operations, two different runtime answers.
5. A Deferred is `{ completion : Option (Prim …), waiters : List WaiterKey }`. Storing the completion as a `Prim` (`Effect4/Runtime/Runtime.lean:93-123`) — not a Lean closure — makes `deferred.done-is-complete-with` and `deferred.interrupt-with` definitional: `done exit = completeWith (Prim.ofExit exit)`, `interruptWith i = done (Exit.failure (Cause.interrupt (some i)))`.
6. `Effect4/Concurrency/Supervision.lean:195-215` (`Fiber.observe` / `Fiber.publish`) is already the waiter protocol: register-if-pending, answer-now-if-done, clear-then-notify-in-registration-order. The Deferred model should be its sibling, not a new invention.
7. Layer needs three things Effect4 does not have: a **scope store** (so a finalizer name can mean an operation on another scope — the open half of `SCOPE-FB-FINALIZER-MEANING`, `docs/SCOPE-DAG.md:228`), the Deferred model, and a **memo world** with a parent chain.
8. `Effect4/Context/Environment.lean` is an 8-line stub, so `layer.build-uses-ambient-scope`, `layer.build-with-memo-map-service` and `scope.acquire-release`'s "captured context" clause have no carrier to be stated over.
9. A Layer must be a *name plus data*: `LayerDesc` with `atom`/`memoized`/`childScope`/`fresh`/`provideWith`/`mergeAll`, and memoization keyed on a `LayerId`, because rc.112 keys the memo `Map` on the layer object (`Layer.ts:390-419`, `:434-443`).
10. The proposed carriers elaborate against the built library. Ref sits at one `Type u`; Deferred and Layer sit at `Type (max u v)`, the `Effect4.Scope` shape. `DecidableEq` derives everywhere **except** `LayerDesc` when `mergeAll` carries `List (LayerDesc ν)` — a nested inductive the handler refuses; `List LayerId` derives.
11. The three traced families are not models. `RefFamily`'s `set` answers `Unit` (`generated/traces/ref/setGet.tsv`, row `answer set []`) so it cannot spell `ref.set-void-returns-cell`; `LayerFamily`'s handler explicitly refuses observer counting, concurrent memo identity and layer composition (`Effect4/Layer/LayerFamily.lean:72-91`).
12. The join lemma is nevertheless cheap and worth stating: each handler is `X.Service (StateT S Id)` (`Effects/Family.lean:39-40`), so "handler = model step under an abstraction relation `S → Model`" is one `funext`-plus-`cases` lemma per family, turning the goldens into checks on the model.
13. `Deferreds` has **no library module at all**: it is declared twice, in `harness/trace/Generate.lean:429-443` and again in `Effect4Test/Flow/DeferredsContract.lean:35-51`. The `effect_signature` DSL pins families at `Effects.Family.{0,0,0}` (`Effect4/Meta/Derive.lean:316`), so a `Type u` model meets a family only at `u = 0`.
14. Of Scope's six `partial` rows, two (`scope.scoped`, `scope.acquire-release`) are *nearly* closable now: `Prim.scopedFrame`, `FrameFiber.uninterruptibleMask` and `restoreAcquire` exist (`Effect4/Runtime/Runtime.lean:2045-2208`) and are already witnesses. What is missing is a fiber *context* field, not a fiber. `scope.fork-linkage` needs only the scope store. `close-sequential`/`close-parallel`/`close-merge` need real fibers.
15. Recommended order: Ref (self-contained), Deferred (needs `Prim`, not the fiber), Layer (needs Scope + Deferred + a scope store + a Context carrier), Scope completion (needs the scope store, then the fiber model). Ref+Deferred+Layer turn 30 rows green and 8 partial without any run-loop work (31 green with the scope-store half of the Scope packet); of the 8, three wait on a Context carrier and five (`await`, `interrupt`, `complete-runs-once`, `merge-parallel-scopes`, `launch-holds-scope`) wait on the fiber packet.

Every claim below is labelled **verified by reading** (I opened the cited span)
or **inferred** (a conclusion drawn from spans I read, not itself written
anywhere).

---

## 1. Census clauses, verbatim

All quotations in this section are **verified by reading**
`generated/effect-runtime-census.tsv` (columns
`mechanism / kind / id / file / lines / span-sha256 / summary`, header at
`:16`). Line numbers are the TSV's own.

### 1.1 `ref.*` — 10 rows, all `absent`, no witness

Coverage rows: `Effect4Test/Audit/RuntimeCoverage.lean:3363-3372`. Nine are
`separateCalculus`; `ref.modify-some-no-reread` is `derivedExpansion`.

| TSV line | id | file:lines | summary |
| --- | --- | --- | --- |
| 117 | `ref.make` | `Ref.ts:142-173` | "A Ref is an object over RefProto whose single field is a fresh MutableRef cell, and make is Effect.sync over that constructor, so every evaluation of the same make effect allocates a distinct cell." |
| 118 | `ref.get` | `Ref.ts:200-200` | "get is a synchronous read of the cell's current field with no copy, so it observes every write already made through any holder of the same Ref." |
| 119 | `ref.set-void-returns-cell` | `Ref.ts:306-307` | "set is declared Effect<void> but its sync thunk returns whatever MutableRef.set returns, so the runtime success value of Ref.set is the mutable cell rather than undefined." |
| 120 | `ref.cell-set-returns-self` | `MutableRef.ts:1063-1070` | "MutableRef.set writes the current field and returns the ref itself, which is the value the void-typed Ref.set thunk produces." |
| 121 | `ref.get-and-set` | `Ref.ts:399-404` | "getAndSet reads current, writes the new value, and returns the value read, all inside one sync thunk, so the read and the write happen with no intervening runtime step." |
| 122 | `ref.set-and-get-assignment` | `Ref.ts:747-747` | "setAndGet succeeds with the value of the assignment expression itself rather than with a second read of the cell." |
| 123 | `ref.update` | `Ref.ts:1273-1276` | "update applies the function to the current value and writes the result back in one sync thunk whose block returns nothing, so the effect succeeds with undefined and the function is applied exactly once per evaluation." |
| 124 | `ref.modify` | `Ref.ts:896-901` | "modify is the general read-modify-write shape: the function maps the current value to a pair, the second component is written back, and the first is the success value." |
| 125 | `ref.modify-some-no-reread` | `Ref.ts:1159-1163` | "modifySome is defined as modify, and on a None second component it writes back the value modify already read rather than re-reading the cell." |
| 126 | `ref.update-some-and-get-reread` | `Ref.ts:1639-1646` | "updateSomeAndGet writes only on Some and then succeeds with a fresh read of current, unlike getAndUpdateSome which succeeds with the value read before the write." |

### 1.2 `deferred.*` — 12 rows, all `absent`, no witness

Coverage rows: `Effect4Test/Audit/RuntimeCoverage.lean:3373-3384`. Eight
`separateCalculus`; `done-is-complete-with`, `complete-runs-once`, `interrupt`,
`interrupt-with` are `derivedExpansion`.

| TSV line | id | file:lines | summary |
| --- | --- | --- | --- |
| 127 | `deferred.make` | `Deferred.ts:140-145` | "A fresh Deferred is an object over DeferredProto with both its waiter array and its completion effect undefined; there is no separate pending tag." |
| 128 | `deferred.is-done` | `Deferred.ts:1382-1382` | "Done-ness is exactly the presence of a stored completion effect, so the state space is undefined or one effect and nothing else." |
| 129 | `deferred.await` | `Deferred.ts:173-186` | "await is a callback effect that resumes at once with the stored effect when the Deferred is already done, and otherwise lazily creates the waiter array, appends its own resume, and returns a cleanup that splices that resume out and does nothing once completion has cleared the array." |
| 130 | `deferred.single-completion` | `Deferred.ts:1648-1650` | "A completion attempt answers false and changes nothing when an effect is already stored, so the first completion wins and every later one is a no-op." |
| 131 | `deferred.completion-order` | `Deferred.ts:1651-1662` | "Completion takes the waiter array and clears the field before resuming, then resumes every waiter in registration order with the stored effect and answers true." |
| 132 | `deferred.complete-with-stores-effect` | `Deferred.ts:456-461` | "completeWith stores the given effect as the completion without running it, so what a waiter is resumed with is that effect rather than a computed result." |
| 133 | `deferred.done-is-complete-with` | `Deferred.ts:570-571` | "done is completeWith itself: completing from an Exit stores that Exit as the completion effect, which is why an Exit completion is shared while an arbitrary effect completion is not." |
| 134 | `deferred.complete-runs-once` | `Deferred.ts:330-335` | "complete suspends so the done check happens at run time, answers false without running the effect when already done, and otherwise runs it through into so its result is memoized." |
| 135 | `deferred.into-uninterruptible` | `Deferred.ts:1774-1784` | "into runs the body under an uninterruptible mask with interruptibility restored only inside, takes the body's Exit, and completes the Deferred with that Exit, so an interrupted body still completes the Deferred." |
| 136 | `deferred.interrupt` | `Deferred.ts:1231-1232` | "interrupt reads the running fiber's id through withFiber and delegates to interruptWith, so the recorded interruptor is the completing fiber, not the awaiting one." |
| 137 | `deferred.interrupt-with` | `Deferred.ts:1332-1337` | "interruptWith completes by failCause of an interrupt cause carrying the given fiber id, so an interrupted Deferred is an ordinary stored failure completion and not a distinguished state." |
| 138 | `deferred.poll` | `Deferred.ts:1414-1416` | "poll is a non-blocking sync read that maps the undefined completion slot to None and a stored completion to Some of that effect." |

### 1.3 `layer.*` — 16 rows, all `absent`, all `separateCalculus`

Coverage rows: `Effect4Test/Audit/RuntimeCoverage.lean:3385-3400`.

| TSV line | id | file:lines | summary |
| --- | --- | --- | --- |
| 139 | `layer.from-build-unsafe` | `Layer.ts:289-298` | "A Layer is an object over LayerProto whose only field is a build function of a memo map and a scope; fromBuildUnsafe installs that function with no scope handling of its own." |
| 140 | `layer.from-build-child-scope` | `Layer.ts:333-345` | "fromBuild forks a child layer scope from the caller scope for the build and closes that child scope only when the build exits in Failure, so a successful build leaves its finalizers attached to the caller scope." |
| 141 | `layer.build-with-memo-map-service` | `Layer.ts:756-765` | "buildWithMemoMap runs the layer's build with the memo map installed as the CurrentMemoMap service and adds that same memo map to the produced context, so nested builds inherit it." |
| 142 | `layer.memo-build-once` | `Layer.ts:390-419` | "The first build of a layer in a memo map allocates a root layer scope and a Deferred, stores an entry with one observer whose effect is that Deferred's await, registers the entry finalizer on the caller scope, builds into the layer scope, and on exit replaces the entry effect with the exit and completes the Deferred, so every other observer shares one build." |
| 143 | `layer.memo-finalizer-last-observer` | `Layer.ts:401-410` | "The memo entry finalizer decrements the observer count on every close, and only the close that brings it to zero deletes the entry from the memo map and closes the layer scope with the closing exit; every other close is void." |
| 144 | `layer.memo-reuse-observer-count` | `Layer.ts:241-250` | "A memo hit increments the entry observer count and registers the same entry finalizer on the new caller scope before yielding the memoized effect, so reuse rebuilds nothing and adds one more close that must happen before the layer scope closes." |
| 145 | `layer.memo-map-parent-lookup` | `Layer.ts:434-443` | "A memo map answers from its own map first, reusing that entry, and otherwise delegates to its parent memo map, so a forked memo map sees layers already built by its parent." |
| 146 | `layer.memo-get-or-else` | `Layer.ts:445-457` | "getOrElseMemoize suspends so the lookup happens at run time, returns the memoized effect on a hit, and otherwise starts exactly one memoMapBuild for that layer." |
| 147 | `layer.current-memo-map-fork-or-create` | `Layer.ts:585-588` | "The memo map for a build is forked from the fiber's CurrentMemoMap when one is present and created fresh otherwise, so an outer build is shared only through the parent chain and never written to." |
| 148 | `layer.build-uses-ambient-scope` | `Layer.ts:800-809` | "Layer.build reads both inputs from the running fiber's context: the memo map by forkOrCreate and the scope by an unchecked Scope service lookup, so a build with no ambient Scope fails in that host lookup rather than as a typed error." |
| 149 | `layer.build-with-scope-still-forks-memo` | `Layer.ts:970-980` | "buildWithScope replaces only the scope; the memo map is still forked or created from the fiber context, so an explicit scope does not imply an explicit memo map." |
| 150 | `layer.merge-parallel-scopes` | `Layer.ts:1587-1602` | "Merging forks one parallel-strategy scope from the caller scope, gives every merged layer its own sequential child of it, builds them all with concurrency equal to the layer count over one shared memo map, and merges the resulting contexts." |
| 151 | `layer.provide-dependency-first` | `Layer.ts:1907-1926` | "provide builds the dependency first on the same memo map and the same scope, provides that context to the dependent layer's build, and combines the two contexts with a function that is identity for provide, so the dependency services do not reach the caller." |
| 152 | `layer.fresh-drops-memoization` | `Layer.ts:3850-3851` | "fresh calls the layer's build directly with a brand new memo map, so the layer is rebuilt even where the ambient memo map already holds it and it gets no fromBuild child scope of its own." |
| 153 | `layer.launch-holds-scope` | `Layer.ts:3897-3898` | "launch builds the layer inside a fresh scope and then runs never, so the built layer stays alive until that effect is interrupted and the scope close runs the acquisition finalizers." |
| 154 | `layer.provide-effect-scope` | `internal/layer.ts:8-22` | "Providing a layer to an effect opens a fresh scope around that effect, builds the layer into it, and provides the resulting context, so the layer's lifetime is exactly the provided program's scope; the local option builds through a private memo map instead of the ambient one." |

### 1.4 The six `partial` `scope.*` rows

Census summaries (TSV lines 71-77) and the coverage row's witnesses and
missing-clause comment (`Effect4Test/Audit/RuntimeCoverage.lean`).

**`scope.close-sequential`** — `internal/effect.ts:3817-3818`. Summary: "The
sequential strategy awaits each finalizer through exit(), capturing failures
instead of throwing." Coverage `:3071-3076`; comment: `missing clause: "awaits
each finalizer through exit()" is temporal sequencing, a fiber-machine fact`.
Witnesses: `Scope.closeExits_eq`, `closeExits_length`, `closeResult_reasons`.

**`scope.close-parallel`** — `internal/effect.ts:3819-3821`. Summary: "The
parallel strategy is immediate daemon forks that inherit the closing fiber
mask, not a separate scheduler policy." Coverage `:3077-3081`; comment:
`missing clause: "immediate daemon forks that inherit the closing fiber mask"
is a fiber-machine fact`. Witnesses: `FinalizerStrategy.cases_receipt`,
`Scope.close_strategy_irrelevant`.

**`scope.close-merge`** — `internal/effect.ts:3823-3826`. Summary: "Parallel
finalizer fibers are awaited together and every exit is merged by
exitAsVoidAll." Coverage `:3082-3088`; comment: `missing clause: "parallel
finalizer fibers are awaited together" is a fiber-machine fact`. Witnesses:
`Scope.closeResult_nil`, `closeResult_single`, `closeResult_many`,
`closeResult_reasons`.

**`scope.fork-linkage`** — `internal/effect.ts:3833-3844`. Summary: "A child
scope of a Closed parent is born Closed with the parent exit; otherwise one
shared key links a parent finalizer closing the child to a child finalizer
removing itself from the parent." Coverage `:3095-3105`; comment: `missing
clause: that the linked names are scopeClose(child, exit) and
scopeRemoveFinalizerUnsafe(parent, key) needs a scope store`. Eight witnesses,
`Scope.fork_closed_parent` … `fork_detach`.

**`scope.scoped`** — `internal/effect.ts:3937-3947`. Summary: "scoped installs
a fresh scope in the fiber context and closes it with the fiber Exit through an
OnExit frame, restoring the previous context first." Coverage `:3106-3121`;
comment: `missing clauses: "installs a fresh scope in the fiber context" and
"restoring the previous context first"`. Thirteen witnesses, including
`Prim.scopedFrame_eq`, `Prim.scopedFrame_finalizer_masked`,
`FrameFiber.step_scopedFrame` — so the OnExit-frame clause is already carried.

**`scope.acquire-release`** — `internal/effect.ts:3970-3987`. Summary:
"acquireRelease runs under uninterruptibleMask, restores interruptibility for
the acquire only when asked, and registers the release against the ambient
scope with the captured context." Coverage `:3122-3135`; comment: `missing
clause: "with the captured context" needs a Context carrier`. Eleven witnesses,
including `FrameFiber.uninterruptibleMask_eq`, `interruptibleRegion_masked`,
`restoreAcquire_asked`, `restoreAcquire_not_asked` — so the mask clauses are
already carried.

Note the drift between the two documents: `docs/SCOPE-DAG.md:147` still lists
`"runs under uninterruptibleMask"` and `"restores interruptibility … only when
asked"` as left-over clauses for `scope.acquire-release`, while
`RuntimeCoverage.lean:3123` names only the context clause and lists the mask
theorems as witnesses. The coverage row is newer and is the authority
(`docs/RUNTIME-COVERAGE.md:44` requires the row comment to list what is
missing). **Verified by reading** both.

---

## 2. The rc.112 mechanisms

All spans in this section: **verified by reading**
`vendor/effect-4.0.0-rc.112/src/`.

### 2.1 Ref

**State.** One field, one indirection.

```ts
export interface Ref<in out A> extends Ref.Variance<A>, Pipeable {
  readonly ref: MutableRef.MutableRef<A>
}
```
(`Ref.ts:59-61`). `MutableRef` holds `current` (`MutableRef.ts:75`,
`:118-120`). `makeUnsafe` is `Object.create(RefProto)` plus
`self.ref = MutableRef.make(value)` (`Ref.ts:142-146`); `make` is
`Effect.sync(() => makeUnsafe(value))` (`Ref.ts:173`).

| Field | Read by | Written by |
| --- | --- | --- |
| `self.ref` | every operation | `makeUnsafe` only |
| `self.ref.current` | `get`, `getUnsafe`, and the pre-read of every RMW | `set` (via `MutableRef.set`), `getAndSet`, `setAndGet`, `update`, `getAndUpdate`, `updateAndGet`, `updateSome`, `getAndUpdateSome`, `updateSomeAndGet`, `modify`, `modifySome` |

**Operations.** Every one is `Effect.sync` of a single thunk; none is
`suspend`, `withFiber`, or a callback effect. Two are defined in terms of
another operation.

| op | source | thunk body | success value |
| --- | --- | --- | --- |
| `make` | `:173` | `makeUnsafe(value)` | the new `Ref` |
| `get` | `:200` | `self.ref.current` | `A` |
| `set` | `:307` | `MutableRef.set(self.ref, value)` | **the `MutableRef`** |
| `getAndSet` | `:399-404` | read `current`; assign; `return current` | pre-value |
| `getAndUpdate` | `:496-501` | read; assign `f(current)`; `return current` | pre-value |
| `getAndUpdateSome` | `:635-643` | read; `pf(current)`; assign on `Some`; `return current` | pre-value |
| `setAndGet` | `:747` | `self.ref.current = value` (expression body) | **the assignment's value**, i.e. `value` |
| `modify` | `:896-901` | `const [b, a] = f(current)`; assign `a`; `return b` | `B` |
| `modifySome` | `:1159-1163` | `modify(self, v => { const [b,o] = pf(v); return [b, o._tag === "None" ? v : o.value] })` | `B` |
| `update` | `:1273-1276` | block body, assigns, **returns nothing** | `undefined` |
| `updateAndGet` | `:1368` | `self.ref.current = f(self.ref.current)` (expression body) | the new value |
| `updateSome` | `:1502-1508` | block body, assigns on `Some`, returns nothing | `undefined` |
| `updateSomeAndGet` | `:1639-1646` | `pf(current)`; assign on `Some`; `return self.ref.current` | **a fresh read after the write** |
| `getUnsafe` | `:1672` | — | `A` (not an Effect) |

The quirks the census names, exactly:

- `MutableRef.set` is `(self, value) => { self.current = value; return self }`
  (`MutableRef.ts:1067-1070`). `Ref.set` is `Effect.sync(() =>
  MutableRef.set(self.ref, value))` (`Ref.ts:307`), an *expression* arrow, so
  the cell is the success value. `Ref.update` (`:1273-1276`) is a *block*
  arrow, so `undefined` is. Both are declared `Effect<void>`.
- `modifySome` is literally `modify` (`:1160`) with the `None` branch writing
  back `value` — the value `modify` already read at `:898` — not a re-read.
- `updateSomeAndGet` (`:1645`) re-reads `self.ref.current` after the write;
  `getAndUpdateSome` (`:637`, `:642`) returns the value read before it. That
  is the pair the census row contrasts.
- `setAndGet` (`:747`) succeeds with the assignment expression, so it never
  reads the cell a second time; `updateAndGet` (`:1368`) is the same shape.

### 2.2 Deferred

**State.** Two optional fields, no tag.

```ts
export interface Deferred<in out A, in out E = never> extends Deferred.Variance<A, E>, Pipeable {
  effect?: Effect<A, E>
  resumes?: Array<(effect: Effect<A, E>) => void> | undefined
}
```
(`Deferred.ts:58-61`). `makeUnsafe` sets both to `undefined`
(`Deferred.ts:140-145`); `make` is `internalEffect.sync(() => makeUnsafe())`
(`:171`).

| Field | Read by | Written by |
| --- | --- | --- |
| `effect` | `isDoneUnsafe`, `poll`, `_await`, `complete`, `doneUnsafe` | `doneUnsafe` only, and only once |
| `resumes` | `_await`, `_await`'s cleanup, `doneUnsafe` | `_await` (lazy create + push), the cleanup (splice), `doneUnsafe` (set to `undefined`) |

**Operations.**

| op | source | kind | reads / writes | answers |
| --- | --- | --- | --- | --- |
| `make` | `:171` | `sync` | writes a fresh cell | the `Deferred` |
| `isDoneUnsafe` | `:1382` | pure | `effect !== undefined` | `boolean` |
| `isDone` | `:1366` | `sync` | as above | `boolean` |
| `poll` | `:1414-1416` | `sync` | `Option.fromUndefinedOr(self.effect)` | `Option<Effect>` |
| `await` (`_await`) | `:173-186` | **`callback`** | done → `resume(self.effect)`; else `resumes ??= []`, `push(resume)` | `A` / parks |
| `doneUnsafe` | `:1648-1661` | pure | the whole protocol | `boolean` |
| `completeWith` | `:458-460` | `sync` | `doneUnsafe(self, effect)` | `boolean` |
| `done` | `:571` | — | **`= completeWith as any`** | `boolean` |
| `succeed` | `:1514` | — | `done(self, core.exitSucceed(value))` | `boolean` |
| `fail` | `:669` | — | `done(self, core.exitFail(error))` | `boolean` |
| `failCause` | `:877` | — | `done(self, core.exitFailCause(cause))` | `boolean` |
| `die` | `:1087` | — | `done(self, core.exitDie(defect))` | `boolean` |
| `failSync`/`failCauseSync`/`dieSync`/`sync` | `:776`, `:985`, `:1194`, `:1618` | `suspend` | evaluate then delegate | `boolean` |
| `complete` | `:333-334` | **`suspend`** | done → `succeed(false)`; else `into(effect, self)` | `boolean` |
| `into` | `:1776-1783` | `uninterruptibleMask` + `exit` | runs the body, completes with its `Exit` | `boolean` |
| `interrupt` | `:1231-1232` | **`withFiber`** | `interruptWith(self, fiber.id)` | `boolean` |
| `interruptWith` | `:1334-1336` | — | `failCause(self, causeInterrupt(fiberId))` | `boolean` |

The quirks, exactly:

- **Single completion and waiter order** are one function
  (`Deferred.ts:1648-1661`): `if (self.effect) return false`; store; then, if
  `resumes` exists, **read it into a local, set the field to `undefined`, and
  only then loop `for (let i = 0; i < resumes.length; i++) resumes[i](effect)`**.
  The source carries the reason in a comment at `:1652-1654`: a waiter resumed
  with an interrupt cause dies synchronously inside `resume`, and its await
  cleanup would otherwise splice the array mid-iteration and skip the next
  waiter. Clear-before-resume is therefore load-bearing, exactly as
  state-before-finalizers is for `scopeCloseUnsafe`.
- **`completeWith` stores an effect, not a value** (`:458-460` → `doneUnsafe`
  at `:1650`): the argument primitive is assigned to `self.effect` and never
  run. A waiter is resumed with *that primitive*.
- **`done` is `completeWith`** (`:571`, a bare `as any` alias). Since `Exit` is
  an `Effect`, completing from an `Exit` stores the `Exit`. That is why an
  `Exit` completion is shared and an arbitrary effect completion is re-run per
  awaiter — the "shared" half is a property of the *stored value*, not of a
  second mechanism.
- **Interrupt is an ordinary stored failure** (`:1334-1336`): `interruptWith`
  is `failCause(self, causeInterrupt(fiberId))`, `failCause` is
  `done(self, exitFailCause(cause))`, `done` is `completeWith`. No third state.
- **`interrupt`'s interruptor is the completing fiber** (`:1231-1232`):
  `core.withFiber((fiber) => interruptWith(self, fiber.id))`.
- **`await`'s cleanup** (`:178-185`) reads `self.resumes`, returns immediately
  if it is `undefined` (which is what completion left behind), otherwise
  `indexOf` + `splice(index, 1)`.
- `_await` is `internalEffect.callback`, which is `callbackOptions(...)`
  (`internal/effect.ts:1163-1169`) — the `op.Async` mechanism.

### 2.3 Layer

**State.** Three records.

```ts
export interface Layer<in ROut, out E = never, out RIn = never> … {
  /** @internal */
  build(memoMap: MemoMap, scope: Scope.Scope): Effect<Context.Context<ROut>, E, RIn>
  …
}
```
(`Layer.ts:54-60`).

```ts
type MemoMapEntry = {
  observers: number
  effect: Effect<Context.Context<any>, any>
  readonly finalizer: (exit: Exit.Exit<unknown, unknown>) => Effect<void>
}
```
(`Layer.ts:235-239`). `MemoMapImpl` (`Layer.ts:421-458`) holds
`readonly parent: MemoMap | undefined` and `readonly map = new Map<Layer, MemoMapEntry>()`.

| Field | Read by | Written by |
| --- | --- | --- |
| `layer.build` | every build path | `fromBuildUnsafe` only (`:289-297`) |
| `entry.observers` | the entry finalizer (`:403-405`) | `memoMapReuse` (`++`, `:245`), the entry finalizer (`--`, `:403`) |
| `entry.effect` | `memoMapReuse` (`:248`), a memo hit | `memoMapBuild` sets it to `Deferred.await(deferred)` (`:400`), then to the exit (`:415`) |
| `entry.finalizer` | `memoMapReuse` (`:247`), `memoMapBuild` (`:412`) | never |
| `memoMap.map` | `MemoMapImpl.get` (`:438`) | `memoMapBuild` (`:411`), the entry finalizer's delete (`:405`) |
| `memoMap.parent` | `MemoMapImpl.get`'s fallback (`:442`) | the constructor (`:428-430`) |

**Operations.**

| op | source | reads | writes | answers |
| --- | --- | --- | --- | --- |
| `fromBuildUnsafe` | `:289-298` | — | `self.build = build` | a `Layer` |
| `fromBuild` | `:333-345` | caller scope | forks a child layer scope, `onExit` closes it **only on Failure** | a `Layer` |
| `fromBuildMemo` | `:380-388` | — | `fromBuild((m, s) => m.getOrElseMemoize(self, s, build))` | a `Layer` |
| `memoMapReuse` | `:241-250` | `entry` | `entry.observers++`; registers `entry.finalizer` on the new scope | `entry.effect` |
| `memoMapBuild` | `:390-419` | — | allocates a layer scope and a `Deferred`, stores an entry with `observers: 1` and `effect: Deferred.await(deferred)`, `map.set`, registers the finalizer on the *caller* scope, builds into the layer scope, `onExit` sets `entry.effect = exit` and `Deferred.done(deferred, exit)` | the context |
| entry finalizer | `:401-410` | `entry.observers` | `--`; on zero: `map.delete(layer)` and `Scope.close(layerScope, exit)` | `void` otherwise |
| `MemoMapImpl.get` | `:434-443` | own `map`, then `parent` | via `memoMapReuse` | the memoized effect or `undefined` |
| `getOrElseMemoize` | `:445-457` | — | `suspend`; `get` then `memoMapBuild` | the context effect |
| `CurrentMemoMap.forkOrCreate` | `:585-588` | the given `Context` | — | `forkMemoMapUnsafe(current)` or `makeMemoMapUnsafe()` |
| `buildWithMemoMap` | `:756-765` | — | `provideService(map(self.build(memoMap, scope), Context.add(CurrentMemoMap, memoMap)), CurrentMemoMap, memoMap)` | the context |
| `build` | `:800-809` | `core.withFiber`: `fiber.context` twice | — | `buildWithMemoMap(self, forkOrCreate(fiber.context), Context.getUnsafe(fiber.context, Scope.Scope))` |
| `buildWithScope` | `:970-980` | `core.withFiber`: `fiber.context` for the memo map only | — | as above with the given scope |
| `mergeAllEffect` | `:1587-1602` | caller scope | forks one `"parallel"` scope, and for each layer one `"sequential"` child of it | `Context.mergeAll` of the results, at `concurrency: layers.length` |
| `provideWith` | `:1907-1926` | — | `fromBuild((memoMap, scope) => …)`: builds `that` first on **the same memoMap and scope**, then `self.build(memoMap, scope)` under `provideContext(context)`, then `f(merged, context)` | the combined context |
| `provide` | `:2345-2348` | — | `provideWith(self, that, identity)` | — |
| `provideMerge` | `:2797-2805` | — | `provideWith(self, that, (self, that) => Context.merge(that, self))` | — |
| `fresh` | `:3850-3851` | — | `fromBuildUnsafe((_, scope) => self.build(makeMemoMapUnsafe(), scope))` | a `Layer` |
| `launch` | `:3897-3898` | — | `internalEffect.scoped(andThen(build(self), internalEffect.never))` | `never` |
| `provideLayer` | `internal/layer.ts:8-22` | — | `scopedWith(scope => flatMap(local ? buildWithMemoMap(layer, makeMemoMapUnsafe(), scope) : buildWithScope(layer, scope), ctx => provideContext(self, ctx)))` | the program's value |

The quirks, exactly:

- **Observer counting and the last-observer finalizer** (`:401-410`): the
  finalizer is a `suspend` that decrements unconditionally and only acts at
  zero — `map.delete(layer)` then `Scope.close(layerScope, exit)`; otherwise
  `void`. A memo hit registers *the same finalizer object* on the new caller
  scope (`:243`), so the number of registered closes equals the observer count.
- **Parent lookup** (`:434-443`): own map first, `memoMapReuse` on a hit,
  otherwise `this.parent?.get(layer, scope)` (`:442`). A parent hit therefore also
  increments the *parent's* entry and registers the parent's finalizer on the
  child's caller scope.
- **`fresh`** (`:3851`) calls `self.build` *directly* with a brand new memo
  map, and installs it with `fromBuildUnsafe`, so the wrapper gets no
  `fromBuild` child scope of its own — both halves of the census clause are in
  that one line.
- **`launch`** (`:3898`) is `scoped(andThen(build(self), never))`; `never` is
  `callback<never>(constVoid)` (`internal/effect.ts:1172`), i.e. `op.Async`.
- **`provide` dependency-first** (`:1915-1925`): the `flatMap`'s first argument
  is `that`'s build, and `self.build` runs inside the continuation with the
  dependency's context provided; the combiner is `identity` for `provide`, so
  the dependency's services do not reach the caller.
- **Merge parallel scopes** (`:1596-1599`): `Scope.forkUnsafe(scope,
  "parallel")` once, then `Scope.forkUnsafe(parentScope, "sequential")` per
  layer, with `{ concurrency: layers.length }` and one shared `memoMap`.
- **`buildWithScope` still forks the memo map** (`:974-979`): only the scope
  argument is replaced; the memo map is still `forkOrCreate(fiber.context)`.

### 2.4 Scope, and the fork/`fiberRunIn` linkage sites

`Scope.State` is `Empty | Open { finalizerKey, finalizer, finalizers } |
Closed { exit }` (`Scope.ts:99-187`). The machinery is in `internal/effect.ts`:
`scopeCloseUnsafe` (`:3779-3798`), `scopeCloseFinalizers` (`:3806-3827`),
`scopeForkUnsafe` (`:3834-3844`), `scopeAddFinalizerExit` (`:3847-3858`),
`scopeAddFinalizerUnsafe` (`:3867-3888`), `scopeRemoveFinalizerUnsafe`
(`:3891-3904`), `scopeMakeUnsafe` (`:3915-3922`), `scoped` (`:3938-3947`),
`scopedWith` (`:3962-3968`), `acquireRelease` (`:3971-3987`), `exitAsVoidAll`
(`:2025-2038`).

The three fiber-facing sites:

- `scopeCloseFinalizers` (`:3806-3827`) materialises
  `Array.from(finalizers.values())`, iterates backwards, and per finalizer
  either `exits.push(yield* exit(finalizer(exit_)))` (sequential, `:3818`) or
  `fibers.push(forkUnsafe(parent, finalizer(exit_), true, true, "inherit"))`
  (parallel, `:3820`). `parent` is `getCurrentFiber()!` (`:3814`). Then
  `exits = yield* fiberAwaitAll(fibers)` (`:3824`) and
  `return yield* exitAsVoidAll(exits)` (`:3826`). `forkUnsafe`'s signature
  (`:5264-5272`) makes `true, true, "inherit"` mean *immediate*, *daemon*, and
  *inherit the parent's `interruptible` flag*.
- `forkIn` (`:5355-5379`): a non-exited child registers, under a fresh key, the
  finalizer `() => withFiberId(interruptor => interruptor === fiber.id ? void_
  : fiberInterrupt(fiber))` on the scope, and `fiber.addObserver(() =>
  scopeRemoveFinalizerUnsafe(scope, key))`. A `Closed` scope instead
  interrupts the child at once (`:5374`). `forkScoped` (`:5400-5406`) is
  `flatMap(scope, scope => forkIn(self, scope, options))`.
- `fiberRunIn` (`:5447-5461`): the same shape without the self-interrupt guard
  — `scopeAddFinalizerUnsafe(scope, key, () => fiberInterrupt(self))` plus an
  observer that removes the key.

`scoped` (`:3938-3947`) is `withFiber(fiber => { const prev = fiber.context;
const scope = scopeMakeUnsafe(); fiber.setContext(Context.add(fiber.context,
scopeTag, scope)); return onExitPrimitive(self, exit => { fiber.setContext(prev);
return scopeCloseUnsafe(scope, exit) }) })`. `acquireRelease` (`:3971-3987`) is
`contextWith(context => uninterruptibleMask(restore => flatMap(scope, scope =>
tap(options?.interruptible ? restore(acquire) : acquire, a =>
scopeAddFinalizerExit(scope, exit => provideContext(release(a, exit),
context))))))`.

---

## 3. Model shape per family

Labels: the carriers below were **elaborated** — see §3.5. The clause-to-theorem
assignments are **inferred** from §1 and §2.

### 3.0 Shared conventions

- Keys are structures over `Nat` at `Type 0` (`RefKey`, `DeferredKey`,
  `WaiterKey`, `LayerId`, `ScopeKey`, `MemoMapId`), embedded into `Type u`
  carriers without `ULift`. rc.112 mints fresh *objects*; the index is the
  model's stand-in and needs a refusal row of the `SCOPE-FB-KEY-IDENTITY`
  shape (`docs/SCOPE-DAG.md:226`, theorem
  `Effect4/Runtime/Scope.lean:318`). **Inferred.**
- A step is `Op → Store → Option (Answer × Store)`. `none` is a *frontier* — a
  key no allocation of this store minted — never a typed error, per
  `AGENTS.md:62-64`. **Verified by reading** `AGENTS.md`.
- DB-02 (`docs/DESIGN-BASIS.md:103-113`) forbids Lean functions in canonical
  content, so every function-valued argument of rc.112 becomes a *name* plus a
  `PrimInterp`-style parameter (`Effect4/Runtime/Runtime.lean:188-215`).

### 3.1 Ref

```lean
structure RefKey where index : Nat            -- Type 0, DecidableEq, Repr, Inhabited
abbrev RefHeap (α : Type u) : Type u := List α

structure RefInterp (ν : Type u) (α β : Type u) : Type u where
  total         : ν → α → α                -- update, getAndUpdate, updateAndGet
  partialUpdate : ν → α → Option α         -- updateSome, getAndUpdateSome, updateSomeAndGet
  modify        : ν → α → β × α            -- modify
  modifySome    : ν → α → β × Option α     -- modifySome

inductive RefOp (ν α : Type u) : Type u
  | make (initial : α) | get (ref : RefKey) | set (ref : RefKey) (value : α)
  | getAndSet … | setAndGet … | update (ref : RefKey) (f : ν) | getAndUpdate …
  | updateAndGet … | updateSome … | getAndUpdateSome … | updateSomeAndGet …
  | modify (ref : RefKey) (f : ν) | modifySome (ref : RefKey) (pf : ν)

inductive RefAnswer (α β : Type u) : Type u
  | void | value (a : α) | result (b : β) | cell (ref : RefKey)

def refStep (I : RefInterp ν α β) : RefOp ν α → RefHeap α → Option (RefAnswer α β × RefHeap α)
def refPeek : RefHeap α → RefKey → Option α
def refPoke : RefHeap α → RefKey → α → RefHeap α
```

The `cell` arm exists solely for `ref.set`. `refStep` is `Option`-valued so a
dangling key is a frontier.

Theorem statements, one line per census clause:

| Row | Clause | Theorem (Lean-ish prose) |
| --- | --- | --- |
| `ref.make` | single field is a fresh cell | `refStep_make : refStep I (.make a) heap = some (.cell ⟨heap.length⟩, heap ++ [a])` |
| | `make` is `Effect.sync` | `make_is_sync : the primitive of a make is `Prim.sync` and `FrameFiber.step` of it succeeds with the allocated key` |
| | every evaluation allocates a distinct cell | `make_twice_distinct : the key of the second make of a heap differs from the key of the first` |
| `ref.get` | synchronous read, no copy | `refStep_get : refPeek heap r = some a → refStep I (.get r) heap = some (.value a, heap)` |
| | observes every write through any holder | `get_after_set : refStep I (.get r) (refPoke heap r v) = some (.value v, refPoke heap r v)` for any holder of `r` |
| `ref.set-void-returns-cell` | declared `void` | `set_declared_void : the declared answer spelling of set is `void`` (a lowering-side receipt, not a step fact) |
| | success value is the cell | `refStep_set : refStep I (.set r v) heap = some (.cell r, refPoke heap r v)` |
| | contrast | `set_answer_ne_update_answer : (.cell r) ≠ (.void : RefAnswer α β)` |
| `ref.cell-set-returns-self` | `MutableRef.set` returns `self` | `refStep_set_answers_self : (refStep I (.set r v) heap).map Prod.fst = some (.cell r)` — the same `r` that was written |
| `ref.get-and-set` | returns the value read | `refStep_getAndSet : refPeek heap r = some a → refStep I (.getAndSet r v) heap = some (.value a, refPoke heap r v)` |
| | one sync thunk, no intervening step | `getAndSet_is_one_step : getAndSet is one `refStep`, not `get` then `set`` — stated as: no heap other than `heap` and `refPoke heap r v` occurs in its trace |
| `ref.set-and-get-assignment` | succeeds with the assignment | `refStep_setAndGet : refStep I (.setAndGet r v) heap = some (.value v, refPoke heap r v)` |
| | not a second read | `setAndGet_ne_reread : the answer is `v` even where `refPeek (refPoke heap r v) r ≠ some v`` — vacuous on a live key, so the sharp form is `setAndGet_answer_eq_argument` |
| `ref.update` | applies `f` and writes back | `refStep_update : refPeek heap r = some a → refStep I (.update r f) heap = some (.void, refPoke heap r (I.total f a))` |
| | succeeds with `undefined` | `refStep_update_answers_void : (refStep I (.update r f) heap).map Prod.fst = some .void` |
| | applied exactly once | `update_applies_once : the resulting cell is `I.total f a`, not `I.total f (I.total f a)`` |
| `ref.modify` | general RMW | `refStep_modify : refPeek heap r = some a → I.modify f a = (b, a') → refStep I (.modify r f) heap = some (.result b, refPoke heap r a')` |
| | second component written, first answered | `modify_components : the answer is `.result b` and the new cell is `a'`, and swapping them is a different function` (the `E4-SEM-CE-015` shape) |
| `ref.modify-some-no-reread` | defined as `modify` | `modifySome_eq_modify : refStep I (.modifySome r pf) = refStep I (.modify r f)` whenever `I.modify f a = (I.modifySome pf a).1, (I.modifySome pf a).2.getD a` |
| | `None` writes back the read value | `refStep_modifySome_none : (I.modifySome pf a).2 = none → the new cell is `a`, the value already read` |
| `ref.update-some-and-get-reread` | writes only on `Some` | `refStep_updateSomeAndGet_none : I.partialUpdate pf a = none → = some (.value a, heap)` |
| | succeeds with a fresh read | `refStep_updateSomeAndGet_some : I.partialUpdate pf a = some a' → = some (.value a', refPoke heap r a')` |
| | unlike `getAndUpdateSome` | `updateSomeAndGet_ne_getAndUpdateSome : ∃ heap r pf, the two answers differ` |

**Dependencies.** None beyond `Prim` for the `make_is_sync` receipt. All ten
rows are provable without the fiber model. **Inferred.**

### 3.2 Deferred

```lean
structure DeferredKey where index : Nat
structure WaiterKey   where index : Nat

structure DeferredCell (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v) where
  completion : Option (Prim ν σ β ε δ ι α)
  waiters    : List WaiterKey

abbrev DeferredHeap … := List (DeferredCell ν σ β ε δ ι α)

inductive DeferredOp … 
  | make | isDone (cell) | poll (cell)
  | awaitOn (cell) (waiter) | awaitCleanup (cell) (waiter)
  | completeWith (cell) (effect : Prim ν σ β ε δ ι α)
  | doneWith (cell) (exit : Exit β ε δ ι α)
  | interruptWith (cell) (interruptor : ι)

inductive DeferredAnswer …
  | handle (cell) | flag (b : Bool) | slot (completion : Option (Prim …))
  | resumeNow (effect : Prim …) | parked (waiter) | woke (waiters : List WaiterKey) (effect : Prim …)

def deferredStep : DeferredOp … → DeferredHeap … → Option (DeferredAnswer … × DeferredHeap …)
```

Storing the completion as a `Prim` is the DB-02-respecting spelling of rc.112's
`effect?: Effect<A, E>`: it is first-order, it already has `DecidableEq`
(`Effect4/Runtime/Runtime.lean:123`), and it already has `Prim.ofExit`
(`:492-495`). `PrimInterp` (`:191-215`) is where the meaning of a stored
non-exit completion comes from; the state model needs none of it.

`woke` is the wake list. It is an *answer*, not a side effect, for the same
reason `Effect4.Scope.close` pairs the state with `closeResult`
(`Effect4/Runtime/Scope.lean:807-809`): it makes "clear before resume" a
theorem instead of a promise.

| Row | Clause | Theorem |
| --- | --- | --- |
| `deferred.make` | both fields undefined | `deferredStep_make : = some (.handle ⟨heap.length⟩, heap ++ [⟨none, []⟩])` |
| | no separate pending tag | `DeferredCell.cases_receipt : a cell is exactly a `completion` slot and a waiter list; there is no third field` |
| `deferred.is-done` | done-ness is presence of the effect | `deferredStep_isDone : cellAt heap c = some cell → = some (.flag cell.completion.isSome, heap)` |
| | state space is undefined or one effect | `DeferredCell.completion_cases : cell.completion = none ∨ ∃ e, cell.completion = some e` |
| `deferred.await` | done → resume at once | `await_done : cell.completion = some e → deferredStep (.awaitOn c w) heap = some (.resumeNow e, heap)` (heap unchanged: no waiter appended) |
| | else lazily create and append | `await_pending : cell.completion = none → = some (.parked w, setCell heap c ⟨none, cell.waiters ++ [w]⟩)` |
| | cleanup splices its own resume out | `awaitCleanup_removes : (deferredStep (.awaitCleanup c w) heap).waitersOf c = cell.waiters.erase w`, order-preserving |
| | cleanup does nothing after completion | `awaitCleanup_after_completion : cell.waiters = [] → deferredStep (.awaitCleanup c w) heap = some (_, heap)` |
| | *it is a callback effect* | **blocked**: `op.Async` (census 23, `absent`) |
| `deferred.single-completion` | answers false, changes nothing | `completeWith_done : cell.completion = some e → deferredStep (.completeWith c e') heap = some (.flag false, heap)` |
| | first wins | `completeWith_first_wins : two completions in sequence leave `some e₁`` |
| `deferred.completion-order` | clears before resuming | `completeWith_clears_first : the resulting cell's `waiters` is `[]` in the same state the `woke` list is read from` — the analogue of `Scope.close_state_independent_of_run` |
| | resumes in registration order | `completeWith_resume_order : deferredStep (.completeWith c e) heap = some (.woke cell.waiters e, setCell heap c ⟨some e, []⟩)` — `cell.waiters`, not reversed |
| | answers true | `completeWith_pending_answers_true` (folded into the equation above; keep as a separate one-liner for the census clause) |
| `deferred.complete-with-stores-effect` | stores without running | `completeWith_stores_argument : ∀ e, the resulting completion is `some e`, for every `Prim` including a non-exit one` |
| | waiter gets that effect | `await_receives_stored : awaiting after `completeWith c e` answers `.resumeNow e`` |
| `deferred.done-is-complete-with` | `done` is `completeWith` | `doneWith_eq_completeWith : deferredStep (.doneWith c x) = deferredStep (.completeWith c (Prim.ofExit x))` — `rfl` by construction |
| | an `Exit` completion is shared | `doneWith_shared : (Prim.ofExit x).asExit? = some x`, so every awaiter observes the same exit (`Prim.ofExit_asExit?`, `Runtime.lean:514`) |
| | an arbitrary effect completion is not | **blocked**: needs each awaiter to *run* the stored primitive — the fiber model |
| `deferred.complete-runs-once` | `complete` suspends | `complete_is_suspend : the primitive of complete is `Prim.suspend`, so the done check is a `step`, not a construction` |
| | answers false without running | `complete_done : cell.completion = some _ → the suspended body is `Prim.success false`` |
| | otherwise `into`, so memoized | **blocked**: "memoized" is a statement about running the effect once |
| `deferred.into-uninterruptible` | uninterruptible mask, restored inside | `into_frame : intoFrame body c = Prim.onSuccess (Prim.exitFrame (masked body)) (doneName c)` with `FrameFiber.uninterruptibleMask` (`Runtime.lean:2070`) and `restoreAcquire true` (`:2075`) |
| | takes the body's `Exit` | `into_takes_exit : the value handed to `doneWith` is the body's `Exit`` (via `Prim.exitFrame`, `Runtime.lean:116`) |
| | an interrupted body still completes | `into_completes_on_interrupt : body exit = .failure (interrupt cause) → the cell ends `some (Prim.ofExit that exit)`` |
| `deferred.interrupt` | reads the running fiber's id | **blocked**: `FrameFiber` (`Runtime.lean:221-233`) has no id field; `Prim.withFiber_refused` (`:2179-2183`) is the standing refusal |
| | delegates to `interruptWith` | `interrupt_eq : given a fiber id `i`, `interrupt = interruptWith i`` — statable, conditional on the id |
| `deferred.interrupt-with` | `failCause` of an interrupt cause | `interruptWith_eq : deferredStep (.interruptWith c i) = deferredStep (.doneWith c (.failure (Cause.interrupt (some i))))` |
| | an ordinary stored failure, not a state | `interrupted_not_distinguished : the resulting cell has the same shape as any other completion` (`DeferredCell.cases_receipt` again) |
| `deferred.poll` | non-blocking sync read | `poll_no_write : deferredStep (.poll c) heap = some (_, heap)` |
| | `undefined ↦ None`, stored ↦ `Some` | `poll_slot : = some (.slot cell.completion, heap)` |

**Dependencies.** `Prim` and `Exit`/`Cause`. Nine of twelve rows are fully
statable without a fiber. `deferred.await` goes to `partial` (state half green,
callback half blocked on `op.Async`); `deferred.interrupt` to `partial` (id);
`deferred.complete-runs-once` to `partial` (memoization). **Inferred.**

**Reuse note.** `Effect4/Concurrency/Supervision.lean:195-215` already has this
protocol for fibers: `Fiber.observe` answers `.value exit` when
`published? = some exit` and otherwise appends a `Subscription` and answers
`.waiting key`; `Fiber.publish` empties `subscriptions` and returns the
per-subscription observations. The Deferred model should be written as its
sibling — same order discipline, same clear-then-notify — and a later packet
should state the one-line correspondence rather than letting two waiter
protocols drift. **Verified by reading.**

### 3.3 Layer

```lean
structure LayerId   where index : Nat
structure ScopeKey  where index : Nat
structure MemoMapId where index : Nat
inductive CombineMode | provide | provideMerge

inductive LayerDesc (ν : Type u) : Type u
  | atom (construction : ν)                       -- fromBuildUnsafe: the build's name
  | memoized (inner : LayerDesc ν)                -- fromBuildMemo
  | childScope (inner : LayerDesc ν)              -- fromBuild
  | fresh (inner : LayerDesc ν)
  | provideWith (self that : LayerDesc ν) (mode : CombineMode)
  | mergeAll (layers : List LayerId)
abbrev LayerTable (ν : Type u) : Type u := List (LayerDesc ν)

structure MemoEntry (ν σ) (β) (ε δ ι α) where
  observers : Nat
  effect : Prim ν σ β ε δ ι α       -- Deferred.await, then Prim.ofExit
  layerScope : ScopeKey
  deferred : DeferredKey
  finalizer : ν

structure MemoMap … where
  id : MemoMapId
  parent : Option MemoMapId
  entries : List (LayerId × MemoEntry …)
abbrev MemoWorld … := List (MemoMap …)

abbrev ScopeStore (κ φ) (β) (ε δ ι α) := List (ScopeKey × Scope κ φ β ε δ ι α)

structure LayerWorld (ν σ κ φ) (β) (ε δ ι α) where
  layers : LayerTable ν
  memo : MemoWorld …
  scopes : ScopeStore …
  deferreds : DeferredHeap …
  nextScope nextMemoMap nextDeferred : Nat

structure LayerInterp (ν σ κ φ) (β) (ε δ ι α) where
  constructionExit  : ν → ScopeKey → Exit β ε δ ι α
  registrations     : ν → ScopeKey → List (κ × φ)
  entryFinalizerName : LayerId → MemoMapId → φ
  awaitName         : DeferredKey → Prim ν σ β ε δ ι α

inductive LayerOp …
  | buildWithMemoMap (layer : LayerId) (memoMap : MemoMapId) (scope : ScopeKey)
  | buildWithScope … | build … | getOrElseMemoize … | memoGet …
  | runEntryFinalizer (layer : LayerId) (memoMap : MemoMapId) (exit : Exit β ε δ ι α)
  | launch (layer : LayerId) | provideLayer (layer : LayerId) (isLocal : Bool)

def layerStep (I : LayerInterp …) : LayerOp … → LayerWorld … → Option (Exit β ε δ ι α × LayerWorld …)
```

Three design points. **Inferred.**

- **Layer identity is `LayerId`, not the description.** rc.112 keys the memo
  `Map` on the layer *object* (`Layer.ts:411`, `:438`), and `fromBuildMemo`
  ties `self` to itself (`Layer.ts:386`). A `LayerId` index into a declared
  `LayerTable` is the model's stand-in; a `LAYER-FB-LAYER-IDENTITY` refusal row
  of the `SCOPE-FB-KEY-IDENTITY` shape is owed. Keying on `LayerDesc` would be
  wrong: two structurally equal declarations are two memo entries on the host.
- **The build is a name plus data.** `atom` carries `ν`; `LayerInterp` supplies
  the construction's exit and the finalizers it registers. This is `PrimInterp`
  (`Runtime.lean:191-215`) applied one level up.
- **The scope store is new and unavoidable.** `Effect4.Scope` is a single
  scope; `memoMapBuild` operates on two (the caller's and the layer's) and the
  entry finalizer closes the layer scope from the caller's. That is exactly the
  open half of `SCOPE-FB-FINALIZER-MEANING` (`docs/SCOPE-DAG.md:228`): the
  store is what lets a finalizer name *mean* `scopeClose(other, exit)`.

| Row | Clause | Theorem |
| --- | --- | --- |
| `layer.from-build-unsafe` | one field, a build of `(memoMap, scope)` | `LayerDesc.atom_arity : an atom's build reads exactly a `MemoMapId` and a `ScopeKey`` (a shape receipt on `layerStep`) |
| | no scope handling of its own | `fromBuildUnsafe_no_fork : layerStep (.buildWithMemoMap ⟨atom⟩ m s) leaves `nextScope` unchanged` |
| `layer.from-build-child-scope` | forks a child layer scope | `childScope_forks : the world after gains one scope forked from `s`` (over `Scope.fork`, `Scope.lean:1036`) |
| | closes it only on Failure | `childScope_closes_on_failure : constructionExit = .failure _ → the child is `Closed`; `.success _` → it stays `Open`` |
| | success leaves finalizers on the caller | `childScope_success_keeps_finalizers : the caller scope still carries the child-closing key` |
| `layer.build-with-memo-map-service` | memo map installed as `CurrentMemoMap` | **blocked**: needs a `Context` carrier; `Effect4/Context/Environment.lean` is a stub |
| | same map added to the produced context | **blocked**, same |
| `layer.memo-build-once` | allocates a layer scope and a Deferred | `memoBuild_allocates : nextScope and nextDeferred each advance by one` |
| | entry with one observer whose effect is the await | `memoBuild_entry : the new entry is ⟨1, I.awaitName d, sc, d, I.entryFinalizerName l m⟩` |
| | registers the entry finalizer on the caller scope | `memoBuild_registers_on_caller : the caller scope's finalizers gain `(k, entryFinalizerName l m)`` |
| | builds into the layer scope | `memoBuild_builds_into_layer_scope : the construction's registrations land on `sc`, not on the caller` |
| | on exit replaces the effect and completes the Deferred | `memoBuild_onExit : entry.effect = Prim.ofExit exit ∧ the deferred heap is `deferredStep (.doneWith d exit)`` |
| | every other observer shares one build | `memoBuild_shared : a second `memoGet` answers `entry.effect`, and no second entry is created` |
| `layer.memo-finalizer-last-observer` | decrements on every close | `entryFinalizer_decrements : observers' = observers - 1` |
| | zero deletes and closes with the closing exit | `entryFinalizer_zero : observers = 1 → the entry is removed and `Scope.close` runs on the layer scope with that exit` |
| | every other close is void | `entryFinalizer_nonzero : observers > 1 → the answer is `Exit.void` and no scope closes` |
| `layer.memo-reuse-observer-count` | increments | `memoReuse_increments : observers' = observers + 1` |
| | registers the same finalizer on the new scope | `memoReuse_registers : the new caller scope gains `entry.finalizer`, and it is the same name` |
| | rebuilds nothing | `memoReuse_no_construction : the layer scope, the deferred and `nextScope` are unchanged` |
| `layer.memo-map-parent-lookup` | own map first | `memoGet_local_first : an own entry is reused and the parent is not consulted` |
| | otherwise the parent | `memoGet_parent : no own entry → the answer is the parent's, and it is the *parent's* observers that increment` |
| | a forked map sees the parent's layers | `forked_sees_parent : after `forkMemoMap p`, `memoGet` of a layer built in `p` hits` |
| `layer.memo-get-or-else` | suspends, so lookup is at run time | `getOrElseMemoize_is_suspend : the primitive is `Prim.suspend`` |
| | hit returns the memoized effect | `getOrElseMemoize_hit : = entry.effect` |
| | miss starts exactly one build | `getOrElseMemoize_miss_one : the world gains exactly one entry for that layer` |
| `layer.current-memo-map-fork-or-create` | fork when present | `forkOrCreate_present : parent = some m` |
| | create fresh otherwise | `forkOrCreate_absent : parent = none` |
| | outer build shared only through the chain, never written | `forkOrCreate_readonly : the parent map's `entries` list is unchanged by a build in the child` (its `observers` may still change — see the parent-lookup row; the clause is about *entries*) |
| `layer.build-uses-ambient-scope` | memo map by `forkOrCreate`, scope by unchecked lookup | **blocked**: `Context` carrier |
| | a missing ambient Scope fails in the host lookup, not as a typed error | `build_no_ambient_scope_is_frontier : `layerStep (.build l none none) = none`` — a frontier per `AGENTS.md:62`, once the Context carrier exists |
| `layer.build-with-scope-still-forks-memo` | only the scope is replaced | `buildWithScope_forks_memo : nextMemoMap still advances` |
| `layer.merge-parallel-scopes` | one parallel-strategy child of the caller | `mergeAll_parent_scope : the new scope's strategy is `.parallel`` |
| | each layer a sequential child of it | `mergeAll_child_scopes : one `.sequential` child per layer, in list order` |
| | one shared memo map | `mergeAll_one_memo_map : every child build uses the same `MemoMapId`` |
| | concurrency equal to the layer count | **blocked**: fiber model |
| | merges the resulting contexts | **blocked**: `Context` carrier |
| `layer.provide-dependency-first` | dependency first, same map and scope | `provideWith_order : the dependency's build precedes and uses the same `(m, s)`` |
| | provided to the dependent's build | **partial**: the ordering is statable; "provides that context" needs `Context` |
| | identity combiner for `provide` | `provide_combine_identity : mode = .provide → the combiner is `identity`` |
| | dependency services do not reach the caller | **blocked**: `Context` |
| `layer.fresh-drops-memoization` | build called directly with a new map | `fresh_new_map : `layerStep (.buildWithMemoMap ⟨fresh l⟩ m s)` uses a fresh `MemoMapId` with `parent = none`` |
| | rebuilt even where the ambient map holds it | `fresh_ignores_ambient : a hit in `m` is not consulted` |
| | no `fromBuild` child scope of its own | `fresh_no_child_scope : the build runs on `s`` |
| `layer.launch-holds-scope` | builds inside a fresh scope | `launch_scope : one fresh scope, closed by an `OnExit` frame` (`Prim.scopedFrame`, `Runtime.lean:2156`) |
| | then runs `never` | **blocked**: `never` is `op.Async` |
| `layer.provide-effect-scope` | fresh scope around the program | `provideLayer_scope : `scopedWith`'s scope is fresh and closed with the program's exit` |
| | lifetime is exactly the program's scope | `provideLayer_lifetime : the built layer's finalizers are on that scope` |
| | `local` builds through a private memo map | `provideLayer_local : isLocal = true → a fresh `MemoMapId` with `parent = none`; false → `buildWithScope`'s forked one` |

**Dependencies.** Scope (`Effect4/Runtime/Scope.lean`), Deferred (§3.2), a
scope store, and a `Context` carrier for five clauses. Layer cannot be packeted
before Deferred: `memoMapBuild`'s entry effect *is* a `Deferred.await`.
**Inferred.**

### 3.4 What Scope needs for the six partial rows

See §5. In carrier terms: a `ScopeStore` (shared with Layer), a `FiberId` field
on the frame fiber or a separate fiber carrier, and a `Context` carrier.

### 3.5 Elaboration check

**Verified by running.** The carriers above were written to a scratch file
importing `Effect4.Runtime.Runtime` and `Effect4.Runtime.Scope` and elaborated
with `lake env lean` against the built library. Result: **it typechecks**, with
two `linter.unusedVariables` warnings on the two placeholder step functions
(`refStep`, `layerStep`, whose bodies are `fun _ _ => none`) and no errors.

Findings from the check:

- **Universes.** `RefKey`, `DeferredKey`, `WaiterKey`, `LayerId`, `ScopeKey`,
  `MemoMapId`, `CombineMode` are `Type 0` and embed into `Type u` inductives
  with no `ULift`. `RefOp ν α : Type u` and `RefAnswer α β : Type u` need one
  universe. `DeferredCell`, `DeferredOp`, `DeferredAnswer`, `MemoEntry`,
  `MemoMap`, `LayerWorld`, `LayerOp`, `LayerInterp` all sit at
  `Type (max u v)` because they mention `Prim ν σ β ε δ ι α` and
  `Exit β ε δ ι α` with `β : Type v` — the same shape as
  `Effect4.Scope κ φ β ε δ ι α : Type (max u v)`
  (`Effect4/Runtime/Scope.lean:86-91`).
- **`DecidableEq`.** Derives for every carrier, including the ones containing
  `Prim` (which itself derives at `Runtime.lean:123`), given the component
  instances. One exception, and it is a real design constraint:
  **`deriving DecidableEq` on `LayerDesc` fails when `mergeAll` carries
  `List (LayerDesc ν)`** — `None of the deriving handlers for class
  DecidableEq applied to LayerDesc`, a nested inductive. Carrying
  `List LayerId` derives cleanly (and is the right model anyway, since
  memoization keys on identity). A packet that wants `mergeAll (layers : List
  (LayerDesc ν))` must hand-write the mutual `decEq`, roughly 30 lines.
- `Repr` and `Inhabited` derive for the key structures; `Inhabited` does not
  derive for `RefOp`/`DeferredOp` without an `Inhabited α`, which is fine.

---

## 4. Joining the model to the traced family

### 4.1 What the handlers are today

**Verified by reading.**

`effect_signature X` (`Effect4/Meta/Derive.lean:250-344`) emits:
`X.Name` (an inductive, `deriving DecidableEq, Repr`, `:313`);
`X.Param : X.Name → Type` and `X.Answer : X.Name → Type` (`:314-315`);
`X : Effects.Family.{0, 0, 0}` (`:316`) — **universe 0 in all three
positions**; `X.Sig` (`:317`); one smart constructor per operation (`:297`);
`X.rows : ServiceRow` (`:320`); `X.Name.spelling`, `X.encodeParam`,
`X.encodeAnswer` (`:326-328`); `X.traced` (`:329-331`);
`X.answerDefault` (`:337-338`); and `X.tracedExcept` (`:340-344`).

A handler is an `Effects.Family.Service X M = ∀ name, X.Param name → M (X.Answer name)`
(`.lake/packages/effects/Effects/Family.lean:39-40`), and
`Service.toHandler` turns it into a `Handler X.toSignature M` (`:42-44`).

| Family | Declared in | Handler | Target monad |
| --- | --- | --- | --- |
| `Refs`, `ERefs` | `Effect4/Stateful/RefFamily.lean:62-72`, `:168-173` | `refsLive`, `erefsLive` (`:86-109`, `:175-191`) | `StateT RefStore Id` with `RefStore := List Nat` (`:77`) |
| `Deferreds` | **no library module**: `harness/trace/Generate.lean:429-443`, re-declared in `Effect4Test/Flow/DeferredsContract.lean:35-51` | `deferredsTraced` (`Generate.lean:501-512`) over `deferredStep` (`:467-489`) | `DeferredM := ExceptT Stall (StateT (DeferredTable × Trace.Log) Id)` (`:495`), `DeferredTable := List (Option (Except Nat Nat))` (`:449`) |
| `Layers` | `Effect4/Layer/LayerFamily.lean:98-106` | `layersLive` (`:149-184`) | `StateT LayerStore Id` with `LayerStore` at `:124-137` |

The trace goldens are produced by `refGoldenLog` (`RefFamily.lean:213-217`),
`deferredGoldenLog` (`Generate.lean:518-525`), `layerGoldenLog`
(`LayerFamily.lean:250-254`), each an `interpret … .toHandler program` run from
an empty store.

### 4.2 The lemma shape

**Inferred.** For each family, the join is an abstraction function from the
family's store to the model's store plus a per-operation simulation:

```lean
def refAbs : RefFamily.RefStore → Scratch.RefHeap Nat := id
def refOpOf : (n : Refs.Name) → Refs.Param n → Scratch.RefOp Name Nat
def refAnsOf : (n : Refs.Name) → Scratch.RefAnswer Nat Nat → Refs.Answer n

theorem refsLive_is_refStep (I : RefInterp …) (n : Refs.Name) (p : Refs.Param n) (s : RefStore) :
    (refsLive n p).run s
      = ((refAnsOf n (refStep I (refOpOf n p) (refAbs s)).get!.1),
         (refStep I (refOpOf n p) (refAbs s)).get!.2)
```

with the `.get!` replaced by a hypothesis that the handle is live. In practice:
one `cases n` and six `rfl`s for `Refs`; the same shape for `Layers` (four
operations) and `Deferreds` (seven).

Concretely the packet cost is about 40 lines for `Refs`, 60 for `Deferreds`
(the `ExceptT` layer has to be peeled) and 60 for `Layers`. Once it exists,
each `#guard` in `Effect4Test/Flow/RefsContract.lean` is a check on the model,
since the golden log is a function of the handler and the handler is the
model's step under `refAbs`. **Inferred.**

Three obstacles, all real:

1. **Universe.** `Effects.Family.{0, 0, 0}` (`Derive.lean:316`) pins the family
   to `Type 0`. The model at `Type u` meets it only at `u = 0`, i.e. with
   `α := Nat`, `β := Nat`, `ν := Nat`. That is fine for the join lemma (the
   goldens are all `Nat`-valued) but it means the lemma is an *instance* of the
   model, not a statement about it.
2. **`Deferreds` has no library home.** It is declared twice (`Generate.lean`
   and `DeferredsContract.lean`), and the contract's own header says so
   (`Effect4Test/Flow/DeferredsContract.lean:9-13`: "The family is re-declared
   here rather than imported: `harness/trace/Generate.lean` is a script, not a
   library"). A join lemma needs a third, library, declaration — or the family
   should be moved to `Effect4/Stateful/DeferredFamily.lean` first, on the
   `RefFamily`/`LayerFamily` precedent.
3. **`Layers.Handle "Ref.Ref<number>"` is not a Layer.** The family's `build`
   answers a service handle, and its store (`LayerStore`, `:124-137`) has no
   memo *map*, no parent chain, no observer count and no Deferred. The join
   would be an abstraction that forgets almost everything.

### 4.3 Where the traced families already diverge from rc.112

**Verified by reading.**

- **`Refs.set` answers `Unit`.** The signature declares
  `set (ref) (value) : Unit` (`RefFamily.lean:66`) and the golden's row is
  `answer	set	[]` (`generated/traces/ref/setGet.tsv`). rc.112 answers the
  `MutableRef` (`Ref.ts:307`). The module says so itself
  (`RefFamily.lean:25-30`): "Both rows are unit here, read off the declared
  spelling and off neither runtime value". The census row
  `ref.set-void-returns-cell` is therefore **not expressible in this family's
  answer profile** — an answer of `Handle "Ref.Ref<number>"` would be needed,
  and `wireAnswer` reads the *declared* spelling, so a `void` declaration
  cannot carry it. This is the single sharpest reason the traced family is not
  the model.
- **`Refs.update` and `Refs.modify` are `+ amount`, not a named function.**
  `refsLive`'s `.update` adds (`RefFamily.lean:97-99`) and `.modify` adds and
  answers the old value (`:100-104`). rc.112's `update` and `modify` take
  arbitrary functions. The census rows `ref.modify-some-no-reread` and
  `ref.update-some-and-get-reread` have no operation in the family at all;
  `RefFamily.lean` records this (`COORDINATION.md:2418-2421`: "The four rows
  about `setAndGet`, `modifySome`, `updateSomeAndGet` and `MutableRef.set` are
  untouched by this lane").
- **`Deferreds` erases the stored *effect*.** `DeferredTable` is
  `List (Option (Except Nat Nat))` (`Generate.lean:449`) — a completion is a
  value or an error, never a primitive. `deferred.complete-with-stores-effect`
  and `deferred.done-is-complete-with`'s "arbitrary effect completion is not
  shared" are outside the alphabet by construction.
- **`Deferreds` has no waiter list.** `deferredStep`'s `.awaitValue` on a
  pending cell is `.error (.pending cell)` (`:484`) — a frontier — and
  `succeed`/`fail` never mention resumes (`:470-477`). So
  `deferred.completion-order` and the cleanup half of `deferred.await` have no
  observable at all. `E4-SEM-CE-013` (`COORDINATION.md:2302-2304`) is exactly
  this: "no function of the projection's table separates the parked run from
  the one a second fiber resumes".
- **`Layers` refuses three census rows explicitly.** `LayerFamily.lean:72-91`:
  observer counting is invisible (`E4-SEM-CE-017`), concurrent memo identity is
  out of reach (`E4-SEM-CE-018`), and layer composition — `provide`, `merge`,
  parent-chain lookup — is refused at this alphabet because "a layer is a build
  function, not a handle" (`E4-SEM-CE-019`). Those are five census rows
  (`memo-reuse-observer-count`, `memo-finalizer-last-observer`,
  `memo-map-parent-lookup`, `provide-dependency-first`,
  `merge-parallel-scopes`) that this family will never witness.
- **`LayerStore.memo : List (Nat × Nat)`** (`LayerFamily.lean:126`) is one flat
  table with no parent and no observer field; `close` empties it wholesale
  (`:183`). rc.112's close decrements per entry.

**Conclusion for Q4.** The join lemma is worth writing for `Refs` and `Layers`
(it converts existing goldens into model checks at no semantic cost), and it is
worth writing for `Deferreds` only after the family moves into the library.
But in all three cases the join is *forgetful*: the family's alphabet is
strictly coarser than the model's, and the goldens will check a projection of
the model, not the model. That should be stated in the packet rather than
discovered by a reader. **Inferred.**

---

## 5. Scope's six partial rows

Frozen obligations: `docs/SCOPE-DAG.md:141-147` (the census-row table),
`:226-229` (the four `SCOPE-FB-*` refusals),
`test/contracts/scope.contract.md:545-547` (capture-not-throw),
`:562-603` (S7, fork linkage), `:609-` (S8, the two brackets). All **verified
by reading**.

### 5.1 `scope.close-sequential`

Missing: "awaits each finalizer through `exit()`". `Effect4.Scope.closeExits`
(`Scope.lean:790-792`) is a total `map` over `closeOrder`, so it already says
every finalizer contributes an exit and none aborts the loop — the
capture-not-throw half. What it cannot say is that finalizer *i+1* begins after
finalizer *i* completes, because the model has no time.

`internal/effect.ts:3818` is `exits.push(yield* exit(finalizer(exit_)))` inside
`fnUntraced(function*…)` — a generator, i.e. a real suspension point per
finalizer. **Blocked on the fiber model**, specifically on a run-loop with a
notion of "the closing fiber resumes after this finalizer's exit". The
`ScopeMachine` (`Effect4/Runtime/ScopeMachine.lean:29-99`) already interprets
one finalizer request at a time and retains the replies, with
`runState_prefix` (`:322`) proving arbitrary-prefix behaviour — that is the
sequencing skeleton. What it lacks is the *fiber* whose step yields between
requests. **Inferred**: this row could reach green with the frame machine alone
if the packet is willing to state sequencing as "the ScopeMachine's request
order is the close order and each reply is consumed before the next request" —
which `ScopeMachine.runState_scope` (`:146`) and `runState_complete` (`:191`)
are close to already. Worth a decision, not an assumption.

### 5.2 `scope.close-parallel`

Missing: "immediate daemon forks that inherit the closing fiber mask".
`internal/effect.ts:3820` is
`forkUnsafe(parent, finalizer(exit_), true, true, "inherit")` and `forkUnsafe`
(`:5264-5272`) reads those three arguments as `immediate`, `daemon`,
`uninterruptible = "inherit"` — the last resolving to
`parentRuntime.interruptible`. `Effect4.Scope.close_strategy_irrelevant`
(`Scope.lean:1022`) is the standing statement that the label selects nothing in
the scope model, deliberately frozen so a later packet must supersede it
(`test/contracts/scope.contract.md:559-562`).

`Effect4/Concurrency/Supervision.lean` has the three pieces: `MaskMode`
(`:15`, with an `inherit` constructor), `ForkOptions` (`:17`), and
`forkUnsafe` (`:244`). **Blocked on joining Supervision's fork to Scope's
close** — not on new carriers. This is the cheapest of the three fiber rows.

### 5.3 `scope.close-merge`

Missing: "parallel finalizer fibers are awaited together". `internal/effect.ts:3823-3826`
is `if (fibers.length > 0) exits = yield* fiberAwaitAll(fibers)` then
`exitAsVoidAll(exits)`. The merge half is green
(`Scope.closeResult_many`, `Exit.asVoidAll_*`). `fiberAwaitAll` is
`internal/effect.ts:779`. Supervision has `WaitState` (`:78`), `WaitState.begin`
(`:286`), `.observe` (`:298`) and the replay theorems the coverage row already
cites for `fork.*`. **Blocked on the fiber model**, but only on wiring
`WaitState` to `closeExits` — the awaiting *carrier* exists.

### 5.4 `scope.fork-linkage`

Missing, per `RuntimeCoverage.lean:3096`: "that the linked names are
`scopeClose(child, exit)` and `scopeRemoveFinalizerUnsafe(parent, key)` needs a
scope store". `Effect4.Scope.fork` (`Scope.lean:1036-1043`) takes the two names
as arguments precisely because DB-02 forbids the closures
(`test/contracts/scope.contract.md:595-599`). The linkage *shape* — one key on
both sides, `fork_shared_key` and `fork_detach` — is already proved.

**Not blocked on the fiber model.** It is blocked on the `ScopeStore` that
§3.3 needs for Layer anyway. Once `ScopeStore` exists, `run : φ → Exit →
ScopeStore → Exit × ScopeStore` can interpret `closeChild` as
`Scope.close` of `ScopeKey` and `detachFromParent` as `Scope.removeUnsafe`, and
the two clauses become equations. **Inferred**; this is the single best
argument for building the scope store early, since it turns a Scope row green
*and* unblocks Layer.

Note the second fiber-facing linkage the census does not have a row for:
`forkIn` (`internal/effect.ts:5355-5379`) and `fiberRunIn` (`:5447-5461`) use
the same key-plus-observer pattern, and `Effect4.Supervision.bindScope`
(`RuntimeCoverage.lean:1383-1389`) already models it for `fork.*`. Scope's
`fork` and Supervision's `bindScope` should share the store.

### 5.5 `scope.scoped`

Missing, per `RuntimeCoverage.lean:3107`: "installs a fresh scope in the fiber
context" and "restoring the previous context first". The `OnExit`-frame clause
is **already carried**: `Prim.scopedFrame` (`Runtime.lean:2156-2157`),
`scopedFrame_finalizer_masked` (`:2166-2172`) and `FrameFiber.step_scopedFrame`
(`:2200-2208`) are witnesses on the row.

`internal/effect.ts:3940-3944` is `const prev = fiber.context; …
fiber.setContext(Context.add(fiber.context, scopeTag, scope)); … onExitPrimitive(self,
exit => { fiber.setContext(prev); … })`. `FrameFiber` (`Runtime.lean:221-233`)
models five fields and the docstring says the `Context` cache is "absent by
construction; the run-loop, supervision and context packets own them".

So: **not blocked on the fiber model — blocked on a `Context` carrier and a
`context` field on the frame fiber.** `Effect4/Context/Environment.lean` and
`Effect4/Context/Service.lean` are 8-line stubs; `Effect4/Context/Key.lean:79`
has `ServiceKey` and `:330-342` a `ServiceUniverse`/`Carrier`, so the key half
exists and the environment half does not. Adding `context : χ` to `FrameFiber`
is exactly what `Supervision.Fiber` already does (`Supervision.lean:32-37`, the
field is `context : χ`). **Inferred.**

### 5.6 `scope.acquire-release`

Missing, per `RuntimeCoverage.lean:3123`: "with the captured context". The mask
clauses are **already carried**: `FrameFiber.uninterruptible_masks`,
`uninterruptibleMask_eq`, `interruptibleRegion_masked`, `restoreAcquire_asked`,
`restoreAcquire_not_asked` (`Runtime.lean:2045-2145`) are on the row.
`Scope.acquireRelease` (`Scope.lean:1377-1382`) uses `tap` semantics — no
release on a failed acquire — and `acquireRelease_registers` (`:1402`) places
the release at the end of the ambient list.

`internal/effect.ts:3976` and `:3983` are `contextWith((context) => …)` and
`provideContext(release(a, exit), context)`. So: **blocked on the same
`Context` carrier as §5.5**, and on nothing else. Not on fibers.

### 5.7 Summary of the six

| Row | Blocked on | Provable today in Scope + frame machine? |
| --- | --- | --- |
| `close-sequential` | temporal sequencing | possibly, via `ScopeMachine`'s request/reply order — needs a decision |
| `close-parallel` | fork mode, daemon flag, mask inheritance | no; needs Supervision's `forkUnsafe` joined to close |
| `close-merge` | `fiberAwaitAll` | no; needs Supervision's `WaitState` joined to `closeExits` |
| `fork-linkage` | a scope store | **yes**, once `ScopeStore` exists — no fiber needed |
| `scoped` | a `Context` carrier and a `context` field on `FrameFiber` | **yes**, once those exist — no fiber needed |
| `acquire-release` | a `Context` carrier | **yes**, once it exists — no fiber needed |

---

## What I could not verify

- **The stated file sizes in the brief are stale.** `Effect4/Runtime/Scope.lean`
  is 1424 lines, not 1250; `Effect4/Stateful/RefFamily.lean` is 255, not 219;
  `Effect4/Layer/LayerFamily.lean` is 324, not 277. The 98-public-theorem count
  I did not recount; `docs/SCOPE-DAG.md:307` also says ninety-eight.
- **`Effect4/Flow/Deferreds`-related declarations do not exist.** The brief
  says to "find them"; there is no `Effect4/Flow/Deferreds*.lean`. The family
  lives in `harness/trace/Generate.lean:429-443` and is re-declared in
  `Effect4Test/Flow/DeferredsContract.lean`. The only other `Deferreds`
  mentions are `Effect4Test/Counterexamples/Flow/Deferreds.lean`,
  `Effect4Test/Flow/DeferredsAxiomReport.lean`,
  `harness/trace/deferred-{fixture,tail}.ts`.
- **I did not run the coverage gate.** `scripts/check-effect-runtime-census.sh`
  and `scripts/report-effect-runtime-coverage.sh` were not run (the brief
  forbids builds and asks for one Lean process at a time). The counts above are
  read directly out of `Effect4Test/Audit/RuntimeCoverage.lean`
  (63 absent / 49 green / 25 partial across 137 rows; 18 `targetOnly` and 2
  `excludedInternal` are outside the denominator, giving 117 and 43). They
  agree with the gate line quoted in `COORDINATION.md:657-661`.
- **The step *functions* were not written.** §3.5 elaborated the carriers and
  the step *signatures*; the bodies are `fun _ _ => none` placeholders. Whether
  each theorem in §3 is `rfl` is therefore not established — I expect most of
  the Ref and Deferred ones to be, on the evidence of
  `Effect4/Layer/LayerFamily.lean:284-322` (eight `rfl` clauses over a
  comparable store) and `Effect4/Runtime/Scope.lean`'s definitional style.
- **Whether `scope.close-sequential` can reach green without a fiber** (§5.1)
  is a judgment about what "awaits" means, not a fact I read. The census
  summary says "awaits each finalizer through `exit()`"; whether the
  ScopeMachine's one-request-at-a-time discipline discharges that clause is a
  coverage decision for the row's owner.
- **`docs/SCOPE-DAG.md:147` and `RuntimeCoverage.lean:3123` disagree** about
  what `scope.acquire-release` still owes (§1.4). I took the coverage row as
  authoritative but did not repair the DAG.
- **`Effect4/Context/Key.lean`** I read only its declaration list
  (`:52-358`), not its semantics; whether `ServiceUniverse`/`Carrier` is the
  right base for the missing `Context` carrier is not something I checked.

---

## Recommended packet shape

Four packets, in this order. Line estimates are calibrated on
`Effect4/Runtime/Scope.lean` (1424 lines for 98 public theorems plus carriers
and docs, so roughly 14 lines per theorem inclusive).

### Packet R — `Effect4/Stateful/Ref.lean`

- **Statements.** `RefKey`, `RefHeap`, `RefInterp`, `RefOp`, `RefAnswer`,
  `refPeek`, `refPoke`, `refStep`; the ~26 theorems of §3.1; one refusal
  theorem `Ref.cell_freshness_refused` in the shape of
  `Scope.key_freshness_refused` (`Scope.lean:318`); one `RefOp.cases_receipt`
  and one `RefAnswer.cases_receipt`.
- **Fence.** `Effect4/Stateful/Ref.lean` (currently an 8-line stub, unclaimed);
  `test/contracts/ref.contract.md`; `Effect4Test/Stateful/RefContract.lean`,
  `RefAxiomReport.lean`; `Effect4Test/Counterexamples/Stateful/Ref.lean`;
  append-only rows in `Effect4Test/Audit/RuntimeCoverage.lean:3363-3372`;
  `docs/REF-DAG.md`. Does **not** touch `Effect4/Stateful/RefFamily.lean`.
- **Size.** ~420 lean lines in `Ref.lean`, ~250 in the battery.
- **Prerequisites.** None. `Prim` only for the one `make_is_sync` receipt; drop
  it if the packet wants zero dependencies.
- **Turns green.** All ten `ref.*` rows. **Partial:** none.

### Packet D — `Effect4/Stateful/Deferred.lean`

- **Statements.** `DeferredKey`, `WaiterKey`, `DeferredCell`, `DeferredHeap`,
  `DeferredOp`, `DeferredAnswer`, `deferredStep`, plus `intoFrame` over
  `Prim`; the ~28 theorems of §3.2; `DeferredCell.cases_receipt`; a refusal
  theorem for "an arbitrary effect completion is not shared" and one for the
  missing fiber id.
- **Fence.** `Effect4/Stateful/Deferred.lean` (8-line stub);
  `test/contracts/deferred.contract.md`;
  `Effect4Test/Stateful/DeferredContract.lean`, `DeferredAxiomReport.lean`;
  `Effect4Test/Counterexamples/Stateful/Deferred.lean`;
  `RuntimeCoverage.lean:3373-3384`; `docs/DEFERRED-DAG.md`.
- **Size.** ~520 lean lines, ~280 battery.
- **Prerequisites.** `Effect4/Runtime/Runtime.lean` (`Prim`, `Exit`, `Cause`,
  `FrameFiber` for the `into` mask clauses). Not the fiber model.
- **Turns green.** `make`, `is-done`, `single-completion`, `completion-order`,
  `complete-with-stores-effect`, `done-is-complete-with`,
  `into-uninterruptible`, `interrupt-with`, `poll` — **9 rows**.
  **Partial:** `await` (state half green, callback half owed to `op.Async`),
  `complete-runs-once` (memoization owed), `interrupt` (fiber id owed) —
  **3 rows**.

### Packet S — `Effect4/Runtime/ScopeStore.lean` + Scope completion

Split out from Layer because it independently closes a Scope row.

- **Statements.** `ScopeKey`, `ScopeStore`, `ScopeStore.get?`/`insert`/`fork`,
  a `FinalizerName` alphabet with `closeChild (child : ScopeKey)` and
  `detachFrom (parent : ScopeKey) (key : κ)`, and a
  `ScopeStore.run : FinalizerName → Exit → ScopeStore → Exit × ScopeStore` that
  interprets them; the two `scope.fork-linkage` clauses as equations
  (`fork_closeChild_means_close`, `fork_detach_means_remove`).
  Then, conditional on a `Context` carrier: a `context` field on `FrameFiber`
  (or a `ContextFiber` wrapper) plus `scoped_installs_and_restores` and
  `acquireRelease_captures_context`.
- **Fence.** New `Effect4/Runtime/ScopeStore.lean`; amendments to
  `docs/SCOPE-DAG.md:145-147` and `:228`;
  `RuntimeCoverage.lean:3095-3135` (comments and witnesses);
  `test/contracts/scope-store.contract.md`. Must **not** edit
  `Effect4/Runtime/Scope.lean` (frozen, 98 theorems).
- **Size.** ~280 lines for the store half; the context half depends on a
  `Context` packet not yet scoped — call it ~200 more once `Environment.lean`
  exists.
- **Prerequisites.** Store half: `Effect4/Runtime/Scope.lean` only. Context
  half: a `Effect4/Context/Environment.lean` packet (currently an 8-line stub)
  — **this is the real prerequisite and it has no owner in `COORDINATION.md`**.
- **Turns green.** `scope.fork-linkage` (store half alone); `scope.scoped` and
  `scope.acquire-release` (with the context half). **Stays partial:**
  `close-sequential`, `close-parallel`, `close-merge`.

### Packet L — `Effect4/Layer/{Description,Memo,Build,Provision}.lean`

- **Statements.** `LayerId`, `CombineMode`, `LayerDesc`, `LayerTable`
  (`Description.lean`); `MemoMapId`, `MemoEntry`, `MemoMap`, `MemoWorld`,
  `memoGet`, `memoReuse`, `memoMapBuild`, `getOrElseMemoize`, `forkOrCreate`,
  the entry finalizer (`Memo.lean`); `LayerWorld`, `LayerInterp`, `LayerOp`,
  `layerStep` (`Build.lean`); `provideWith`, `mergeAllEffect`, `provideLayer`,
  `fresh`, `launch` (`Provision.lean`); the ~48 theorems of §3.3; a
  `LAYER-FB-LAYER-IDENTITY` refusal theorem.
- **Fence.** The four stubs above plus `Effect4/Layer/Laws.lean`;
  `test/contracts/layer.contract.md`; `Effect4Test/Layer/*Contract.lean` and
  `*AxiomReport.lean`; `Effect4Test/Counterexamples/Layer/*.lean`;
  `RuntimeCoverage.lean:3385-3400`; `docs/LAYER-DAG.md`. Does **not** touch
  `Effect4/Layer/LayerFamily.lean`.
- **Size.** ~950 lean lines across the four modules, ~400 battery. This is the
  largest packet by a factor of two and should be split at the `Memo.lean`
  boundary if the fence gets contended.
- **Prerequisites.** Packet D (the memo entry's effect *is* a
  `Deferred.await`), packet S's store half (the entry finalizer closes another
  scope), `Effect4/Runtime/Scope.lean`, and — for five clauses — the Context
  carrier.
- **Turns green.** `from-build-unsafe`, `from-build-child-scope`,
  `memo-build-once`, `memo-finalizer-last-observer`,
  `memo-reuse-observer-count`, `memo-map-parent-lookup`, `memo-get-or-else`,
  `current-memo-map-fork-or-create`, `build-with-scope-still-forks-memo`,
  `fresh-drops-memoization`, `provide-effect-scope` — **11 rows**.
  **Partial:** `build-with-memo-map-service` and `build-uses-ambient-scope`
  (Context), `merge-parallel-scopes` (concurrency + Context),
  `provide-dependency-first` (Context), `launch-holds-scope` (`never` =
  `op.Async`) — **5 rows**.

### Net effect on the metric

R + D + L + S(store half) moves 10 + 9 + 11 + 1 = **31 rows** from `absent` (or
`partial`) to `green` and leaves 8 at `partial`, without a single line of
run-loop work. Adding the Context packet moves 3 more Layer rows and 2 Scope
rows. The last five (`deferred.await`, `deferred.interrupt`,
`deferred.complete-runs-once`, `layer.merge-parallel-scopes`,
`layer.launch-holds-scope`) plus `scope.close-{sequential,parallel,merge}` wait
on the fiber packet, which is the same packet that owes `op.Yield`, `op.Async`
and the two `checkpoint.*` rows. **Inferred**; the exact numbers must be
re-read off the census after each packet, never computed by hand
(`AGENTS.md:104-107`).
