# Lowering lane L3: the store families at the full rc.112 surface

Lane report, 2026-09-03. Pin `effect@4.0.0-rc.112`, upstream
`2600f62f4532026928454dcea8d1c48557b3f942`. Plan row: `docs/research/2026-09-03-deep-plan.md`
§2, L3. Every line number below is into `vendor/effect-4.0.0-rc.112/src/`.

This lane was started by an agent that hit a usage cap mid-flight; everything it
wrote is in `0f5a46d` ("WIP: REFACTOR"). This report covers the whole lane, and
marks what that agent left red.

## Summary

* **Five families, eighty-four rows, all at the full rc.112 surface.** `Refs`
  12, `Deferreds` 16, `Scopes` 16, `Layers` 22, `Contexts` 18. Every handler is
  a projection of a spike-S2 store, and the projection is a lemma rather than a
  paragraph.
* **`Deferreds` and `Scopes` moved out of `harness/trace/Generate.lean` and into
  the library.** A script is not a library: nothing under `Effect4/` could state
  a theorem about either, and both were written out twice. They are
  `Effect4/Stateful/DeferredFamily.lean` and `Effect4/Runtime/ScopeFamily.lean`
  now, the script imports them, and `Effect4Test/Flow/DeferredsContract.lean`
  imports rather than re-declares. Deep plan §5, decision 3, applied and
  extended to `Scopes`.
* **`Layers` was rebuilt on a memo map.** A layer is a
  `Handle "Layer.Layer<number>"` answered by the constructor that made it, so
  the eleven constructors, the two memo-map operations and the three builds are
  rows. `E4-SEM-CE-019`'s third clause — "composition needs a layer *value* on
  the wire and a layer is a build function, not a handle" — is **lifted**.
* **Six batteries, four of them new.** `LayersContract`, `LayersAxiomReport` and
  `Counterexamples/Semantics/Layers` re-pinned; `DeferredsContract` /
  `DeferredsAxiomReport` re-pointed at the library; `ScopesContract` /
  `ScopesAxiomReport` and `ContextsContract` / `ContextsAxiomReport` new;
  `Counterexamples/Runtime/Refs` repaired for the named-function request.
* **`lake build Effect4TestFlow Effect4TestRuntime Effect4TestCounterexamples`
  is green** (139 jobs), and each battery builds by name. §7.
* **One library theorem was over the axiom ceiling and is fixed.**
  `DeferredFamily.cancel_splices_the_waiter` reached `Classical.choice` through
  `beq_self_eq_true`, which the gate refuses under `Effect4/`. It is `[propext]`
  now. §6.
* **`lake build Effect4TestGreen` still fails, on the module-closure gate
  alone**, because the four new battery modules are not reachable from
  `Effect4Test.lean` and this lane may not edit it. The four import lines are
  §8. **No `AxiomGate.lean` entry is needed** — nothing this lane authored
  reaches `Classical.choice`.
* **The eight goldens under `generated/traces/layer/` are owed a
  regeneration**; the four under `generated/traces/scope/` and the six under
  `generated/traces/deferred/` are **unchanged**, byte for byte. §5.

---

## 1. `Refs` — `Effect4/Stateful/RefFamily.lean`

Twelve rows. Handle spellings: `Handle "Ref.Ref<number>"` for a cell,
`Handle "RefFn"` for a named function.

| row | request | answer | rc.112 |
| --- | --- | --- | --- |
| `make` | `initial: number` | `Ref.Ref<number>` | `Ref.ts:173`, `makeUnsafe` `:142-146` |
| `get` | `ref` | `number` | `Ref.ts:200` |
| `set` | `ref, value: number` | `Ref.Ref<number>` — **the cell** | `Ref.ts:307`, `MutableRef.ts:1067-1070` |
| `getAndSet` | `ref, value` | `number` before the write | `Ref.ts:399-404` |
| `setAndGet` | `ref, value` | `number`, the assignment expression | `Ref.ts:747` |
| `update` | `ref, f: RefFn` | `void` | `Ref.ts:1273-1276` |
| `getAndUpdate` | `ref, f: RefFn` | `number` before the write | `Ref.ts:496-501` |
| `updateAndGet` | `ref, f: RefFn` | `number` after the write | `Ref.ts:1368` |
| `modify` | `ref, f: RefFn` | `number`, the pair's first component | `Ref.ts:896-901` |
| `getAndUpdateSome` | `ref, pf: RefFn` | `number` read before the write | `Ref.ts:635-643` |
| `updateSomeAndGet` | `ref, pf: RefFn` | `number`, a fresh read after the write | `Ref.ts:1639-1646` |
| `modifySome` | `ref, pf: RefFn` | `number`; `None` writes back the read value | `Ref.ts:1159-1163` |

Beside it, `ERefs` keeps its three rows (`make`, `tryTake`, `get`) unchanged:
its `tryTake` is the contrasting half of `E4-SEM-CE-015`, where the two tuple
components have different types and the compiler pins the order.

### What changed against the previous six rows

Both changes are cases of *the row was wrong against rc.112*
(`docs/research/2026-09-03-deep-state-models.md` §4.3), not of taste.

* **`set` answers the cell, not `Unit`.** `MutableRef.set` is
  `(self, value) => { self.current = value; return self }`
  (`MutableRef.ts:1067-1070`) and `Ref.set` is an *expression* arrow over it
  (`Ref.ts:307`). The declaration is `Effect<void>` and the previous row read
  the declaration; census row `ref.set-void-returns-cell` is about the runtime
  value. `Ref.update`'s arrow is a *block* (`Ref.ts:1273-1276`) and really does
  answer `undefined`, so the pair is the whole content of the census row and is
  now a theorem, `set_answer_ne_update_answer`.
* **The seven read-modify-write rows take a function, not an amount.** DB-02
  forbids a Lean function in canonical content, so the function is a *name*:
  `Handle "RefFn"`, an index into the five-entry table `RefFns` declares on both
  faces (`fnIncr`, `fnDouble`, `fnTakeAndBump`, `fnNoChange`,
  `fnZeroWhenPositive`), interpreted by `RefFn.total`, `RefFn.partialUpdate`,
  `RefFn.modify` and `RefFn.modifySome`. A program names one with a
  `PureTerm.app`, never with a closure.

### Two rows deliberately not present

* `updateSome` (`Ref.ts:1502-1508`) answers `undefined` like `update` and no
  census clause separates the two.
* `getUnsafe` (`Ref.ts:1672`) is not an `Effect` at all, so it has no service
  method to lower.

---

## 2. `Deferreds` — `Effect4/Stateful/DeferredFamily.lean`

Sixteen rows. Handle spelling: `Handle "Deferred.Deferred<number, number>"`.
The first seven keep their order, spelling and answers, so all six goldens are
unchanged.

| row | request | answer | rc.112 |
| --- | --- | --- | --- |
| `make` | — | the cell | `Deferred.ts:171`, `makeUnsafe` `:140-145` |
| `succeed` | `cell, value: number` | `boolean` | `:1514` |
| `fail` | `cell, error: number` | `boolean` | `:669` |
| `isDone` | `cell` | `boolean` | `:1366`, `isDoneUnsafe` `:1382` |
| `poll` | `cell` | `Option<Result<number, number>>` | `:1414-1416` |
| `awaitValue` | `cell` | `number !! number` | `:173-186` |
| `awaitError` | `cell` | `number !! number` | `:173-186` |
| `awaitDeferred` | `cell` | `Result<number, number>` | `:173-186` |
| `failCause` | `cell, error: number` | `boolean` | `:877` |
| `die` | `cell, defect: number` | `boolean` | `:1087` |
| `interrupt` | `cell` | `boolean` | `:1231-1232` |
| `interruptWith` | `cell, fiber: number` | `boolean` | `:1334-1336` |
| `complete` | `cell, effect: number` | `boolean` | `:333-334` |
| `completeWith` | `cell, effect: number` | `boolean` | `:458-460` |
| `done` | `cell, exit: Result<number, number>` | `boolean` | `:571` |
| `into` | `cell, body: number` | `boolean` | `:1776-1783` |

`await` is a reserved word in the generated-binding profile
(`Effect4/Target/TypeScript/EffectV4.lean` `bindingName` over
`TypeScript.reservedIdentifiers`), so rc.112's `_await` is spelled
**`awaitDeferred`**. The two older rows `awaitValue`/`awaitError` are the same
mechanism read through the two halves of a `Result`; they stay because their
goldens do.

### What the store now carries that the table did not

The previous projection was `List (Option (Except Nat Nat))` and had no waiter
list at all. Both gaps are closed:

* **A completion is a stored effect.** `Completion` has five arms — the exit's
  three outcomes, an interrupt with its interruptor, and `stored`, a *named*
  effect that is assigned and never run (`:458-460` → `:1650`). `succeed`,
  `fail`, `failCause`, `die`, `interrupt`, `interruptWith` and `done` are all
  `doneUnsafe` of one completion (`:571`, `:1648-1662`), which is why they are
  one store operation and not seven.
* **`_await` registers a waiter and a completion clears the list before it
  resumes** (`:173-177`, `:1655-1659`). No row observes the waiter list —
  rc.112 has no entry point that does — so those clauses are theorems about the
  store. That is the whole forgetful direction of this family's join.

---

## 3. `Scopes` — `Effect4/Runtime/ScopeFamily.lean`

Sixteen rows over the frozen `Effect4/Runtime/Scope.lean` state machine, which
is used unchanged (`Scope.make`, `addExit`, `removeUnsafe`, `fork`, `close`,
`closeOrder`) and given no new semantics. Handle spelling:
`Handle "Scope.Closeable"`. The first four keep their spelling and order, so the
four goldens are unchanged.

| row | request | answer | rc.112 |
| --- | --- | --- | --- |
| `make` | — | the scope, at the `"sequential"` default | `Scope.ts:240`, `internal/effect.ts:3915-3922` |
| `addFinalizer` | `scope, key: number` | `boolean` | `Scope.ts:456`, `internal/effect.ts:3867-3888` |
| `remove` | `scope, key` | `void` | `internal/effect.ts:3891-3904` — **no public entry point** |
| `close` | `scope` | `ReadonlyArray<number>`, the keys it ran | `Scope.ts:567`, `internal/effect.ts:3779-3798` |
| `makeWith` | `strategy: number` | the scope | `internal/effect.ts:3915-3922` |
| `fork` | `parent, strategy: number` | the child scope | `Scope.ts:489`, `internal/effect.ts:3834-3844` |
| `addFinalizerExit` | `scope, key` | `boolean` | `Scope.ts:422`, `internal/effect.ts:3847-3858` |
| `closeExit` | `scope, exit: Result<number, number>` | the keys it ran | `internal/effect.ts:3779-3798` |
| `isClosed` | `scope` | `boolean` | `Scope.ts:99-187` |
| `closedWith` | `scope` | `Option<boolean>` | `Scope.ts:99-187` |
| `provide` | `scope, key` | `boolean` | `Scope.ts:310` — **rc.112 has no `Scope.extend`** |
| `use` | `scope, key` | the keys the close ran | `Scope.ts:616` |
| `forkIn` | `scope, fiber: number` | `boolean` | `internal/effect.ts:5355-5379` |
| `runIn` | `scope, fiber: number` | `boolean` | `internal/effect.ts:5447-5461` |
| `linked` | `scope` | `ReadonlyArray<number>` | — (store probe) |
| `exitFiber` | `scope, fiber` | `void` | `internal/effect.ts:5377`, `:5459` |

`SCOPE-FB-FINALIZER-MEANING` (`docs/SCOPE-DAG.md:228`) is **closed** by this
family: the finalizer alphabet `FinName` has `release`, `closeChildScope`,
`detachFromParent` and `interruptFiber`, so a fork registers exactly the pair
rc.112 registers under one shared key, and `close` *runs* the child scopes its
order names. What `close` answers is still this scope's own keys in run order —
the answer the goldens carry — so a cascade is visible through `isClosed` of the
child and never through a longer answer.

---

## 4. `Layers` — `Effect4/Layer/LayerFamily.lean`

Twenty-two rows. Handle spellings: `Handle "Layer.Layer<number>"` (a layer),
`Handle "Layer.MemoMap"`, `Handle "Context.Context<never>"`,
`Handle "Ref.Ref<number>"` (a constructed service),
`Handle "Scope.Closeable"` (a layer scope).

| row | request | answer | rc.112 |
| --- | --- | --- | --- |
| `succeed` | `service: number` | a layer | `Layer.ts:1012` |
| `effect` | `service: number` | a layer | `Layer.ts:1347` |
| `scoped` | `service: number` | a layer | `Layer.ts:1347` over `internal/effect.ts:3938-3947` |
| `provide` | `layer, dependency` | a layer | `Layer.ts:2008`, `provideWith` `:1907-1926` |
| `provideMerge` | `layer, dependency` | a layer | `Layer.ts:2436`, `:2797-2805` |
| `merge` | `left, right` | a layer | `Layer.ts:1705` |
| `mergeAll` | `layers: ReadonlyArray<Layer>` | a layer | `Layer.ts:1652`, `mergeAllEffect` `:1587-1602` |
| `fresh` | `layer` | a layer | `Layer.ts:3850-3851` |
| `memoize` | `layer` | a layer | `fromBuildMemo`, `Layer.ts:380-388` |
| `orDie` | `layer` | a layer | `Layer.ts:3327` |
| `unwrap` | `layer` | a layer | `Layer.ts:1580` |
| `makeMemoMap` | — | a memo map | `Layer.ts:492`, `:545` |
| `forkMemoMap` | `parent` | a memo map | `Layer.ts:511`, `:564`, `MemoMapImpl.get` `:434-443` |
| `build` | `layer` | a context | `Layer.ts:800-809` |
| `buildWithScope` | `layer, scope` | a context | `Layer.ts:863`, `:970-980` |
| `buildWithMemoMap` | `layer, memoMap, scope` | a context | `Layer.ts:645`, `:756-765` |
| `launch` | `layer` | `void` | `Layer.ts:3897-3898` |
| `servicesOf` | `context` | `ReadonlyArray<Ref>` | the built context, read by tag |
| `scopeOf` | `service` | a scope | `memoMapBuild`, `Layer.ts:390-419` |
| `provideCount` | `layer` | `number` | the construction ledger |
| `observers` | `layer` | `number` | `Layer.ts:245`, `:403` |
| `close` | — | `ReadonlyArray<Ref>` in release order | the enclosing scope |

### What changed, and why

The previous family had **four** rows (`build`, `provideCount`, `scopeOf`,
`close`), named a layer by a `Nat`, and carried a table
`memo : List (Nat × Nat)` keyed by layer id, with `freshOf` and `layerBase`
hard-coding one four-layer corpus (layer 3 was `Layer.fresh` of layer 1). All of
that is gone. In its place:

* **`LayerDesc`**, the description a layer handle names, with one arm per
  constructor;
* **`MemoMap`** (`MemoMapImpl`, `Layer.ts:421-458`): a parent and a table of
  `MemoEntry { layer, service, scope, observers }`;
* **`buildMany`**, one fuelled worklist function over which `merge`/`mergeAll`
  flatten, `fresh` allocates a private memo map, `provide` builds the dependency
  first and drops it, `provideMerge` keeps it, and `buildBase` is
  `getOrElseMemoize` (`Layer.ts:445-457`).

The six theorems that named the old carrier (`build_constructs`,
`build_memoizes`, `build_memo_hit`, `build_fresh_ignores_memo`,
`build_after_close_is_not_live`, `build_after_close_is_not_memoized`) are
replaced by eight over the new one. Every *fact* survives:

| old | new |
| --- | --- |
| `build_memo_hit` | `buildBase_memo_hit` |
| `build_constructs`, `build_memoizes` | `buildBase_miss_constructs` |
| `build_fresh_ignores_memo` | the `.fresh` arm of `buildMany` (a private memo map), shown by the `freshRebuild` rows and by `freshBuiltTwice` in the counterexample battery |
| `build_after_close_is_not_live` | `buildBase_after_close_is_not_live` (same name, new carrier) |
| `build_after_close_is_not_memoized` | `close_empties_every_memo_map` |
| — | `declare_takes_the_next_handle`, `memoChain_starts_at_the_map` (new: the handle counter and the parent chain) |
| `close_releases_in_reverse`, `close_is_terminal` | unchanged |

`freshOf` and `layerBase` have no replacement and need none: they were a
hard-coded corpus, and `LayerDesc.fresh` is the general form.

---

## 5. `Contexts` — `Effect4/Context/ContextFamily.lean`

Eighteen rows, and the first Effect4 carrier for a context at all:
`Effect4/Context/Environment.lean` is an eight-line stub, which is why
`layer.build-with-memo-map-service`, `layer.build-uses-ambient-scope` and
`scope.acquire-release`'s "captured context" clause had nothing to be stated
over. Handle spellings: `Handle "Context.Key<never, number>"` and
`Handle "Context.Context<never>"`.

| row | request | answer | rc.112 |
| --- | --- | --- | --- |
| `empty` | — | a context | `Context.ts:853` |
| `key` | `name: number, service: number` | a key | a `Context.Service`/`Context.Reference` tag |
| `referenceKey` | `reference: number` | a key | the four the runtime reads |
| `make` | `key, value: number` | a context | `Context.ts:874-877` |
| `add` | `context, key, value` | a context | `Context.ts:915`, `:990-994` |
| `get` | `context, key` | `number !! number` | `Context.getUnsafe` `:1475-1484`, throws at `:1590` |
| `getOption` | `context, key` | `Option<number>` | `Context.getOrUndefined` `:1636`, `:1705-1709` |
| `merge` | `left, right` | a context | `Context.ts:1745`, `:1816-1820` |
| `pick` | `context, key` | a context | `Context.ts:1904-1913` |
| `omit` | `context, key` | a context | `Context.ts:1946-1954` |
| `provideContext` | `context` | the context it replaced | `internal/effect.ts:2180-2199` |
| `updateContext` | `key, value` | the context it replaced | `internal/effect.ts:2073-2097` |
| `withContext` | — | the fiber's context | `internal/effect.ts:2152-2158` — **rc.112 has no `Effect.withContext`** |
| `keyConflict` | `left, right` | `boolean` | `Effect4.ServiceKey.Conflict` |
| `maxOpsBeforeYield` | — | `number`, default `2048` | `Scheduler.ts:269-272` |
| `preventSchedulerYield` | — | `boolean`, default `false` | `Scheduler.ts:295-298` |
| `currentMemoMap` | — | `Option<Layer.MemoMap>` | `Layer.ts:584-588` |
| `currentScope` | — | `Option<Scope.Closeable>` | `Scope.ts:215`, `internal/effect.ts:3772` |

A key crosses as an index into the store's key table, and the store binds values
by the **`Effect4.ServiceKey`** the index names — a `ServiceName` paired with a
`ServiceTypeCode`, whose identity is the pair. Two `key` requests with the same
name and code answer the same handle; two with the same name and different codes
do not, and `keyConflict` is `ServiceKey.Conflict` on the wire. The four
references reserve the first four service names, so a minted key is offset past
them (`mintedKey name service = ⟨⟨name + 4⟩, ⟨service⟩⟩`); rc.112's own tags are
strings like `effect/Scheduler/MaxOpsBeforeYield` and cannot collide with a user
tag, and the offset is this alphabet's stand-in for that.

---

## 6. Agreement with the L2 host tails, row by row

The L2 lane (`docs/research/2026-09-03-lowering-l2-host-tails.md`) implemented
the same five surfaces against rc.112 and left six stubs at
`harness/trace/{refs,deferreds,scopes,layers,context}-fixture.stub.ts`. The
stubs are what the generated fixtures replace, so every difference below is a
thing the fixture generator will change on one side or the other. **Every
difference is listed.**

### 6.1 `Refs` — 12 Lean rows against 13 host rows

| Lean | host | difference and ruling |
| --- | --- | --- |
| — | `updateSome(ref, floor)` → `void` | **Lean has no row.** `Ref.ts:1502-1508` answers `undefined` exactly as `update` does and no census clause separates them, so the family declines to row it. The host row is harmless; the fixture will not carry it. |
| `set` → `Ref.Ref<number>` | `set` → `MutableRef.MutableRef<number>` | **Real divergence, already a registered refusal.** rc.112's `Ref.set` answers the `MutableRef` *inside* the ref, a different object (`Ref.ts:307`, `MutableRef.ts:1067-1070`); `ref-tail.ts` brands `~effect/MutableRef` (`MutableRef.ts:18`) so the tracer numbers it fresh — L2 §4 observed `op set [0, 9] / answer set 1` where this store answers `0`. Both faces say "the cell is the answer"; the *number* is `E4-SEM-CE-014`, the per-family vs global counter, and is not comparable until the tail reconciles them. Recorded in `RefFamily.lean`'s refusals. |
| `f: RefFn` on seven rows | `amount: number` / `floor: number` | **Spelling.** Both are a number on the wire. The host's argument *parameterises* one fixed function shape; the Lean argument *names* one of five declared functions (`RefFns`, emitted to `harness/trace/ref-fns.ts`). The Lean form is the DB-02 one and the host owes the table. Arity agrees. |

Everything else — `make`, `get`, `getAndSet`, `setAndGet`, `update`,
`getAndUpdate`, `updateAndGet`, `modify`, `getAndUpdateSome`,
`updateSomeAndGet`, `modifySome` — agrees name for name and arity for arity.

### 6.2 `Deferreds` — 16 Lean rows against 15 host rows

| Lean | host | difference and ruling |
| --- | --- | --- |
| `awaitError`, `awaitDeferred` | only `awaitValue` | **Host owes two rows.** Both are the same `_await` (`:173-186`) read differently. `awaitDeferred` inherits L2 §5's found loss: `Effect.result` catches a typed failure and **not** an interrupt, so an interrupted cell cannot be read into a `Result` at all; on the Lean side that is the `unspellable` frontier and `E4-SEM-CE-012`. |
| — | `ran` → `ReadonlyArray<number>` | **Host probe, no Lean row.** It reports which named primitives the tail actually ran, which is host evidence for `deferred.complete-runs-once`; the Lean side states the same fact as `complete_of_done_does_not_run` and `completeWith_stores_the_name`. |
| `done(cell, exit: Result)` | `done(cell, code: number)` | **Lean is closer to rc.112.** `Deferred.done(self, exit)` takes an `Exit` (`:570-571`); the host's `code` is the tail's primitive-table indirection. The fixture should emit the `Result` spelling. |
| `into(cell, body)` | `into(code, cell)` | **Argument order.** rc.112's dual signature is effect-first; every row of this family puts the cell first. No semantic content, but the emitted fixture will carry `into(cell, body)` and the tail must swap. |
| row order | row order | The Lean order is the frozen seven then the nine added; the stub's is `Deferred.ts` documentation order. The emitted class fixes the order, so the tail follows the fixture. |

Everything else agrees name for name and arity for arity.

### 6.3 `Scopes` — 16 Lean rows against 12 host rows

| Lean | host | difference and ruling |
| --- | --- | --- |
| `make` (nullary) + `makeWith(strategy: number)` | `make(parallel: boolean)` + `makeUnsafe(parallel: boolean)` | **Two differences.** (a) The Lean split is `make` at rc.112's own `"sequential"` default (`internal/effect.ts:3915`) plus the argument-taking form, which is what keeps the four goldens byte-identical. (b) The strategy is a `number` (0 sequential, 1 parallel) here and a `boolean` there; the wire alphabet has no string arm on either side and the two picked different encodings. The fixture must settle it — recommend the `number`, since `FinalizerStrategy` is an enumeration and a third label would not fit a boolean. |
| — | `makeUnsafe`, `forkUnsafe` | **Lean collapses each pair.** `Scope.make`/`makeUnsafe` and `Scope.fork`/`forkUnsafe` differ only in being an `Effect` or not (`internal/effect.ts:3915-3930`, `:3830-3844`); every row of this family is an `Effect`, so the two collapse into one. |
| `provide` | `extend` | **Renamed row, one of the five.** rc.112 v4 exports no `Scope.extend`; the operation is `Scope.provide` (`Scope.ts:310` = `internal/effect.ts:3932-3936`). L2 §12.4 asked for the name to be reconsidered at the landing; it is done, and the host row should be renamed to match. |
| `forkIn`, `runIn` → `boolean` | `forkFiberIn`, `runIn` → `Fiber.Fiber<number, number>` | **Name and answer.** The Lean lane has no fiber carrier — a fiber is the `Fibers` family's business — so the row answers whether the scope accepted the link, which is the fact `internal/effect.ts:5374` turns on: a closed scope interrupts the fiber at once and registers nothing. The name follows rc.112's `Effect.forkIn`. |
| `isClosed`, `closedWith`, `linked`, `exitFiber` | `exitsSeen` | **Four store probes against one.** The host's probe reports the exits its finalizers saw; the Lean probes read the state machine. Neither is an rc.112 call and neither claims to be. |
| `remove` | — (in `ScopesFull`) | Kept from the narrow family. It still has no rc.112 entry point: the package's `exports` map sends `./internal/*` to `null`, so `scopeRemoveFinalizerUnsafe` is unreachable and the host performs the same two-arm removal over the public mutable `Scope.state`. The golden pins the state shape and the model, never a call. |
| `closeExit` | — | **Host owes a row.** The host's `close` always uses the void exit; `internal/effect.ts:3779-3798` takes one. |

### 6.4 `Layers` — 22 Lean rows against 15 host rows

| Lean | host | difference and ruling |
| --- | --- | --- |
| `effect(service)` | `declare(base)` | Same row, rc.112's own constructor name (`Layer.ts:1347`). Recommend renaming the host row. |
| `succeed`, `scoped` | — | **Host owes two rows** (`Layer.ts:1012`; `:1347` over `internal/effect.ts:3938-3947`). |
| `mergeAll(layers: ReadonlyArray<Layer>)` | `mergeAll(self, that)` | **Arity.** rc.112's `Layer.mergeAll` is variadic (`:1652-1658`) and deep plan §5 decision 2 rules `LayerDesc.mergeAll` carries `List LayerId`; the host's binary form is a special case. |
| `buildWithScope(layer, scope)` | `buildWithScope(layer)` | **Arity; Lean matches rc.112.** `Layer.buildWithScope(self, scope)` (`:863`) takes the scope; the host tail supplies its own. |
| `buildWithMemoMap(layer, memoMap, scope)` | `buildWithMemoMap(layer, memo)` | **Arity; Lean matches rc.112.** `:645`, `:756-765` takes three. |
| `build(layer)` + `servicesOf(context)` | the two `build*` rows answer `ReadonlyArray<number>` | **A deliberate split.** A built context is an object with an identity, so the build rows answer `Handle "Context.Context<never>"` and `servicesOf` is the read. The host reads the bases back through declared tags inside the build row, which loses the context handle. `build` itself (the ambient-memo-map form, `:800-809`) has no host row at all. |
| `scopeOf`, `observers`, `close` | `provideCount` only | **Three store probes against one.** `observers` is the forgetful direction of the join, §6.6. |
| `memoize` | `memoize` | **Same name, recorded difference.** §6.6. |

### 6.5 `Contexts` — 18 Lean rows against 13 host rows

| Lean | host | difference and ruling |
| --- | --- | --- |
| — | `mergeAll(self, that)` | **Lean owes a row.** `Context.mergeAll` (`Context.ts:1861-1871`) is an rc.112 export and the only entry point of the five surfaces this lane did not row. It is the n-ary fold of `merge` and needs a list-former atom the corpus does not declare (the `LayerAtoms.twoLayers` shape). Recorded in `ContextFamily.lean`'s header; the exact row to add is `mergeAll (contexts : List (Handle "Context.Context<never>")) : Handle "Context.Context<never>"` with the same right-biased fold `merge` already uses. |
| `key`, `referenceKey`, `keyConflict` | — (keys are indices into a tail-local table) | **Host owes a key minter.** Key identity here is the `ServiceKey` *pair*, and `keyConflict` is the row that says so; the host names keys positionally and cannot express the colliding pair. This is `Effect4/Context/Key.lean`'s own standing refusal, now with a wire. |
| `provideContext(context)` | `provide(root, context)` | **Arity.** The host names a declared root because a request cannot carry a program; the Lean row is a point operation that answers the context it replaced. |
| `updateContext(key, value)` | `updateContext(root, key, value)` | Same reason. |
| `withContext` → a context handle | `withContext` → `ReadonlyArray<number>` | **Answer.** The Lean row answers the ambient context's handle (which `getOption` then reads); the host answers the keys present. The names agree, which is why the Lean row keeps the non-rc.112 name — see §6.6. |
| `maxOpsBeforeYield`, `preventSchedulerYield`, `currentMemoMap`, `currentScope` | `referenceDefault` | **Four typed reads against one counter.** The host probe counts how often `defaultValue()` ran (once — it is cached on the reference object); the Lean rows read the values. DB-02 keeps the host's `() => 2048` out of canonical content, so the defaults are values here, read off `Scheduler.ts:271` and `:297` and written down. A reference whose default is an *object* has no value to write down, so `currentMemoMap` and `currentScope` answer `Option` and are `none` until something binds them, which is `Context.getOrUndefined`'s own answer (`Layer.ts:586`). |

### 6.6 The five rc.112 non-public APIs, on the Lean side

L2 §12 found five things rc.112 has no public API for. Each is a refusal row or
a renamed row here. Draft register rows follow; IDs are proposals for the
breaker to allocate, since `test/counterexamples/REGISTER.md` never reuses one.

**(a) The children set — `childrenSnapshot` / `awaitChildren`.** Not L3's
surface: it is the `Fibers` profile, `Effect4/Target/TypeScript/FiberProfile.lean`
(lane L1), which this lane may not edit. The refusal is **owed there** and is
recorded here so it is not lost.

> `E4-TARGET-CE-0nn` | RESERVED | The `Fibers` profile's `childrenSnapshot` and
> `awaitChildren` rows are rc.112 calls | refusal row. The tracked children live
> on the fiber *implementation*: the field is `_children`
> (`internal/effect.ts:534`), the accessor `children()` (`:703-705`), and
> `forkUnsafe` populates it only for a non-daemon fork (`:5279-5282`). The
> public `Fiber.Fiber` interface (`Fiber.ts:70-92`) exposes neither, and the
> package's `exports` map sends `./internal/*` to `null`. The only public
> combinator is the **fused** `Effect.awaitAllChildren` (`Effect.ts:17207`,
> `internal/effect.ts:5314-5334`), which snapshots before and awaits after one
> effect and never hands the snapshot out; `FiberSet` was checked and is not
> that surface | the two rows are a model of rc.112's own state read through a
> documented cast in `harness/trace/fibers-tail.ts`, and stay refusals until
> rc.112 exports the pair.

**(b) A `Layer`'s raw builder.** `Layer.build(memoMap, scope)` is a member of the
exported interface at `Layer.ts:56`, carries `@internal`, and is stripped from
`dist/Layer.d.ts:44-48`. Recorded in `LayerFamily.lean`'s header: this family's
`fresh` models what `Layer.fresh` *does* — build through a private memo map —
rather than how `:3851` spells it, because a consumer cannot write that line.
The `build` row is the exported `Layer.build(self)` (`:800-809`), a different
declaration, and is public.

> `E4-SEM-CE-0nn` | RESERVED | The `Layers` family's `fresh` row is
> `Layer.fresh`'s own spelling | refusal row. `Layer.fresh` is one line at
> `Layer.ts:3851` over the interface member `build(memoMap, scope)` (`:56`),
> which carries `@internal` and is absent from `dist/Layer.d.ts:44-48`, so no
> consumer can write it. `Effect4/Layer/LayerFamily.lean`'s `.fresh` arm of
> `buildMany` allocates a private memo map and builds into it, which is what the
> line does and not how it is written | the row claims the behaviour and not the
> spelling; a golden comparing the two faces compares construction counts and
> memo-map contents, never a builder.

**(c) `Layer.memoize`.** No such export at this pin. Memoization is
`Layer.fromBuildMemo` (`:380-388`), which ties the layer to itself through
`memoMap.getOrElseMemoize(self, scope, build)`; `Layer.effect` and
`Layer.effectContext` are the ordinary route to it (`:1439`, `:1481`). Because
of (b) the only builder a consumer can hand `fromBuildMemo` is
`buildWithMemoMap`, which is `self.build(memoMap, scope)` **plus** installing the
memo map as the `CurrentMemoMap` service and adding it to the produced context
(`:761-765`). `LayerFamily.lean` now records that difference explicitly rather
than claiming `fromBuildMemo ∘ build`.

> `E4-SEM-CE-0nn` | RESERVED | The `Layers` family's `memoize` row is
> `Layer.memoize` | refusal row. rc.112 exports no `Layer.memoize`; memoization
> is `fromBuildMemo` (`Layer.ts:380-388`), which is what `Layer.effect` already
> goes through, so the row is idempotent in the model. On the host the only
> builder a consumer can reach is `Layer.buildWithMemoMap` (`:645`, `:756-765`),
> which additionally installs the memo map as `CurrentMemoMap` and adds it to
> the produced context | the model's `memoize` is the identity on memo
> behaviour; the extra `CurrentMemoMap` binding is not on this wire, and a
> golden that compared built-context contents would see it.

**(d) `Scope.extend`.** Not an export at this pin: the v4 name is
`Scope.provide` (`Scope.ts:310-387` = `internal/effect.ts:3932-3936`,
`provideService(scopeTag)`), and the closing form is `Scope.use` (`:616-661` =
`:3950-3959`). **The Lean row is renamed, not refused**: `ScopeFamily.lean` rows
`provide` and `use` and says so in its header. The host's `extend` row should be
renamed at the landing.

**(e) `Effect.withContext`.** Not an export at this pin: the reader is
`Effect.contextWith` (`Effect.ts:11346` = `internal/effect.ts:2156-2158`) and
`Effect.context()` (`:2152`) is the same read as a value, which is what this
nullary row answers. **The Lean row keeps the name `withContext`** because
`harness/trace/context-tail.ts` and `context-fixture.stub.ts` already carry it,
so the two faces agree name for name; that the name is not an rc.112 export is a
refusal, recorded in `ContextFamily.lean`'s header.

> `E4-SEM-CE-0nn` | RESERVED | The `Contexts` family's `withContext` row is an
> rc.112 export | refusal row. rc.112 exports no `Effect.withContext`; the
> reader is `Effect.contextWith` (`Effect.ts:11346` =
> `internal/effect.ts:2156-2158`, `withFiber(fiber => f(fiber.context))`) and
> `Effect.context()` (`:2152`) is the same read as a value. The row is the
> value read, under a name both faces already carry | the name is the two faces'
> agreement, not a claim about rc.112's surface; `Effect4/Context/ContextFamily.lean`
> and `harness/trace/context-tail.ts` cite `contextWith` in the same breath.

---

## 7. Projection lemmas: the shapes, and which are proved

Every lemma below is **proved**; none is stated with a blocker. Each was
measured with `#print axioms`, and the ceiling is `propext` plus `Quot.sound`.

### `Refs` — `Effect4Test/Flow/RefsAxiomReport.lean`

| lemma | shape | axioms |
| --- | --- | --- |
| `refsLive_is_refStep` | `refsLive name p s = (refAnswerOf name (refRun (refOpOf name p) s).1, (refRun …).2)`, by `rfl` | `propext` |
| `refsLive_of_step` | a live handle takes the step's own value and heap | `propext` |
| `refStep_make`, `refStep_set`, `refStep_update`, `refStep_setAndGet`, `refStep_modifySome_none`, `refStep_updateSomeAndGet_none` | one census clause each | `propext` |
| `set_answer_ne_update_answer` | the two `void`-declared rows do not answer the same thing | `propext` |
| `updateSomeAndGet_ne_getAndUpdateSome` | before-the-write against after-the-write, by `decide` | `propext` |
| `RefFn.ofHandle_index` | reading a handle back is the identity on the table | none |

### `Deferreds` — `Effect4Test/Flow/DeferredsAxiomReport.lean`

Twelve library clauses, all `propext`: `deferredStep_make`,
`deferredStep_succeed`, `done_eq_complete_of_exit`,
`interrupt_is_interruptWith_self`, `completeWith_stores_the_name`,
`complete_twice_is_false`, `complete_clears_then_owes`, `isDone_of_completion`,
`awaitDeferred_pending_registers`, `cancel_splices_the_waiter`,
`cancel_after_complete_is_a_noop`, `complete_of_done_does_not_run`. The contract
restates the six laws the four-row era carried
(`isDone_eq_poll_isSome`, `succeed_once`, `fail_after_succeed`,
`awaitValue_of_completed`, `awaitValue_pending`, `pendingAwait_is_a_frontier`)
over the store the library owns; all `propext`.

The whole content of "the handler is a projection" here is that every completion
row goes through `DeferredStore.complete`, which *is* `doneUnsafe`
(`Deferred.ts:1648-1662`) — one equation, not sixteen.

### `Scopes` — `Effect4Test/Flow/ScopesAxiomReport.lean`

| lemma | shape | axioms |
| --- | --- | --- |
| `fork_registers_the_linkage_names` | a fork registers `closeChildScope key child` on the parent and `detachFromParent key parent` on the child, one shared key | `propext` |
| `close_cascades_to_the_child` | closing the parent closes the child scope its order names, by `decide` | `propext` |
| `close_writes_the_parent_state_first` | the parent's own state is written before any finalizer runs | `propext` |
| `closeOrder_is_the_keys` | `close` answers the materialised registration list, backwards | `propext` |
| `linkFiber_closed_scope` | a closed scope links nothing and answers `false` | `propext` |
| `linkFiber_names` | `forkIn` and `Fiber.runIn` register the same name at different guards | `propext` |

### `Layers` — `Effect4Test/Flow/LayersAxiomReport.lean`

| lemma | shape | axioms |
| --- | --- | --- |
| `declare_takes_the_next_handle` | a declared layer takes the next handle and binds its description | none |
| `memoChain_starts_at_the_map` | `MemoMapImpl.get` looks in its own map first | `propext, Quot.sound` |
| `buildBase_memo_hit` | a hit answers the entry's service and increments the owner's observer count | `propext` |
| `buildBase_miss_constructs` | a miss takes the next handle | `propext` |
| `buildBase_after_close_is_not_live` | a build after `close` never joins the live set | `propext` |
| `close_releases_in_reverse` | `close` answers `live.reverse` | none |
| `close_is_terminal` | `closed := true`, `live := []` | none |
| `close_empties_every_memo_map` | no build after a close can hit an entry | `propext` |

### `Contexts` — `Effect4Test/Flow/ContextsAxiomReport.lean`

| lemma | shape | axioms |
| --- | --- | --- |
| `declareKey_is_by_the_pair` | the same `ServiceKey` answers the same handle twice | `propext, Quot.sound` |
| `minted_keys_conflict` | one name, two type codes, in conflict | none |
| `bind_replaces_in_place` | a later `add` of the same key wins | `propext, Quot.sound` |
| `lookup_bind_self`, `lookup_other` | a binding is read back by its own key and by no other | `propext` |
| `maxOps_default`, `preventYield_default` | `2048` and `false` until something binds them | `propext` (+ `Quot.sound`) |
| `objectReferences_have_no_default` | `CurrentMemoMap` and `Scope` are `none` | `propext` |

### One repair to the library's axiom ceiling

`DeferredFamily.cancel_splices_the_waiter` was proved by `simp` and reached
`[propext, Classical.choice, Quot.sound]`, because the generic
`beq_self_eq_true` goes through `[ReflBEq α]`. `Effect4/` is audited by
`#effect4_axiom_gate` at `propext`/`Quot.sound`, so that would have failed the
gate the moment the module was reachable. `instBEqNat` is
`instBEqOfDecidableEq`, so the fix is a two-line private lemma
(`show decide (n = n) = true; exact decide_eq_true rfl`) and an explicit
`rw [List.filter, h]`. The theorem is `[propext]` now. It is the only
declaration in any of the five families that was over the ceiling.

---

## 8. Builds

```
> lake build Effect4TestFlow Effect4TestRuntime Effect4TestCounterexamples
Build completed successfully (139 jobs).
```

Then each battery by name:

```
Effect4Test.Flow.ScopesContract            -> Build completed successfully (25 jobs).
Effect4Test.Flow.ScopesAxiomReport         -> Build completed successfully (24 jobs).
Effect4Test.Flow.ContextsContract          -> Build completed successfully (23 jobs).
Effect4Test.Flow.ContextsAxiomReport       -> Build completed successfully (22 jobs).
Effect4Test.Flow.LayersContract            -> Build completed successfully (22 jobs).
Effect4Test.Flow.LayersAxiomReport         -> Build completed successfully (21 jobs).
Effect4Test.Flow.DeferredsContract         -> Build completed successfully (21 jobs).
Effect4Test.Flow.DeferredsAxiomReport      -> Build completed successfully (23 jobs).
Effect4Test.Flow.RefsContract              -> Build completed successfully (22 jobs).
Effect4Test.Flow.RefsAxiomReport           -> Build completed successfully (23 jobs).
Effect4Test.Counterexamples.Semantics.Layers -> Build completed successfully (22 jobs).
Effect4Test.Counterexamples.Runtime.Refs   -> Build completed successfully (21 jobs).
```

And the generator elaborates:

```
> lake env lean harness/trace/Generate.lean
GENERATE_EXIT=0
```

`lake build Effect4TestGreen` **fails on one line**, the module-closure gate:

```
error: Effect4Test.lean:140:0: Effect4 module-closure gate:
  …\Effect4Test\Flow\ContextsAxiomReport.lean is not reachable from the Effect4Test audit root
```

That is the four new modules and nothing else; §9 has the import lines.

### What was red before this lane and is green now

`lake build Effect4TestGreen` at `0f5a46d` failed in four modules:

* `Effect4Test.Flow.LayersContract` — `freshOf`, `layerBase`, `build_constructs`,
  `build_memoizes`, `build_memo_hit`, `build_fresh_ignores_memo`,
  `build_after_close_is_not_live`, `build_after_close_is_not_memoized` and
  `LayerStore.memo` all unknown;
* `Effect4Test.Flow.LayersAxiomReport` — the same six theorem names;
* `Effect4Test.Counterexamples.Semantics.Layers` — the same, plus
  `OfNat (Layers.Param Layers.Name.build)` (a layer is a handle now, not a
  `Nat`) and four golden `#guard`s that no longer evaluate;
* `Effect4Test.Counterexamples.Runtime.Refs` — `HAdd Nat (Handle "RefFn")` and
  `OfNat (Handle "RefFn")` (the read-modify-write argument is a named function
  now, not an amount). **This one was not in the lane brief**; it is red for
  exactly the same reason and is repaired here.

---

## 9. The lines the coordinator applies

### `Effect4Test.lean`

Four imports. Put them beside the other family batteries — after
`import Effect4Test.Counterexamples.Runtime.Refs` (line 121) is the natural
place, since `ScopesContract` and `ContextsContract` are family batteries like
`RefsContract`:

```lean
import Effect4Test.Flow.ScopesContract
import Effect4Test.Flow.ScopesAxiomReport
import Effect4Test.Flow.ContextsContract
import Effect4Test.Flow.ContextsAxiomReport
```

### `Effect4Test/Audit/AxiomGate.lean`

> **Correction (coordinator, 2026-09-04).** This was wrong for one declaration
> per atoms block: `RefFns.source`, `DeferredAtoms.source`, `ScopeAtoms.source`
> and `LayerAtoms.source` are `atomsModule` over the rows and reach
> `Classical.choice` through the renderer, as `#print axioms` shows and as the
> gate reported the first time it was reached (`Effect4.RefFamily.RefFns.source`).
> The rows and `eval` dispatchers are clean as stated. The five `<Name>.source`
> declarations (with `ContextAtoms.source`, added for `Context.mergeAll`) are
> now exact roots beside the two battery ones.

**No entry.** Nothing this lane authored reaches `Classical.choice`:

* the five family modules stay at `propext`/`Quot.sound` (§7), so no
  `choiceImplementationDeclarations` entry is owed;
* the batteries render wire rows only inside `#guard`, which is a command and
  leaves no declaration in the environment, so the renderer's crossing is never
  inherited by a constant;
* the only `def`s the new batteries declare are `LayersContract.{declared,
  builtOnce, builtTwice}` and `Counterexamples.Semantics.Layers.{declared,
  builtOnce, builtTwice, freshBuiltTwice}`, all measured axiom-free.

The gate's *staleness* check is the reason to say this explicitly: an entry
added "just in case" for a declaration that does not reach `Classical.choice`
fails the gate.

### Routing note

The four new batteries go under `Effect4Test/Flow/`, not
`Effect4Test/Runtime/`. `docs/AGENT-ROUTING.md` does not fix battery
directories, but the repo's own convention is unambiguous: every traced family's
battery is `Effect4Test/Flow/<Family>Contract.lean` whatever directory the
family module lives in — `Refs` from `Effect4/Stateful/`, `Layers` from
`Effect4/Layer/`, `Fibers` from `Effect4/Concurrency/`. Following it keeps
`Effect4Test/Runtime/Scope{,Machine,Restoration}Contract.lean` as the batteries
of the `Scope` *carrier*, which is a different owner from the `Scopes` family.

---

## 10. What the DSL could not express

Seven things, all worked around rather than blocked; none stopped a row.

1. **A Lean function in a request.** DB-02 forbids it, so every rc.112 argument
   of function type is a *name*: `RefFn` (five entries), the `Deferreds` effect
   table (`runEffect`, two entries), `FinName` (four arms), `LayerDesc` (eleven
   arms). Each name table has to be declared on both faces, and `effect_atoms`
   is what makes that one declaration instead of two.
2. **`effect_atoms` has no nullary former.** `RefFns`' five atoms each take a
   `tag : Nat` binder that both faces ignore, purely so the atom is an
   application; a program writes `Refs.update(r, fnIncr 0)`.
3. **`await` is a reserved generated binding**, so rc.112's `_await` is
   `awaitDeferred`.
4. **A nested inductive's `DecidableEq` handler refuses** (state note §3.5), so
   `LayerDesc.mergeAll` carries `List Nat` and not `List LayerDesc`. That is
   also why the store is a table of `(Nat × LayerDesc)` rather than a tree, and
   it is the reason `buildMany` is a fuelled worklist: the fuel is
   `(layers.length + 1) * (layers.length + 2)`, and the description graph is
   acyclic because a description can only name handles that already existed.
5. **`Family.Service.traced` is an around-wrapper with no access to `M`'s
   state**, so a family cannot emit region or finalizer events. `Scopes.close`
   and `Layers.close` carry the release order as an *answer* instead, which is
   why `close` answers a list of keys and a list of services.
6. **One family per `effect_program`.** A program that forked a child and awaited
   a cell the child completes cannot be spelled, which is `E4-SEM-CE-013`'s owed
   two-fiber golden. It is also why `Layers`' concurrent memo identity
   (`E4-SEM-CE-019`) has no witness: `memoMapBuild` installs a `Deferred` before
   the construction runs, and this alphabet has one fiber.
7. **A frontier needs its own monad.** `Deferreds` cannot use
   `Family.Service.tracedExcept` — it writes a `failed` row for every abort and
   a pending await has no failure to report — so `deferredsTraced` is written by
   hand with the store and the log *below* the error channel. `Contexts` does
   use `tracedExcept`, because its one aborting row (`get`) really is a typed
   failure.

---

## 11. What is owed after this lane

| owed | to whom |
| --- | --- |
| Regenerate `generated/traces/layer/` — eight goldens, all indices moved, `freshRegion` retired, five programs added | harness lane |
| Generate `generated/traces/{context}/` and the full-surface `ref`, `deferred`, `scope` goldens | harness lane |
| Replace the six `*-fixture.stub.ts` with emitted fixtures; the row differences of §6 are what the emission settles | harness lane |
| `harness/trace/ref-fns.ts` — the `RefFn` table on the host | harness lane |
| An observer counter in `harness/trace/layer-tail.ts` before the `observers` row is compared | harness lane |
| The `childrenSnapshot` / `awaitChildren` refusal in `Effect4/Target/TypeScript/FiberProfile.lean` (§6.6a) | lane L1 |
| `Contexts.mergeAll` (§6.5) | a follow-up L3 packet |
| Stable IDs for the four draft register rows of §6.6 | the breaker |
| A counterexample for `provideContext`'s restore — the row answers the replaced context, and that the previous context comes back when the provided effect finishes is a frame fact, not a service call | a follow-up packet |

### Register rows edited by this lane

`test/counterexamples/REGISTER.md`, four rows, all because the witness they name
changed:

* **`E4-SEM-CE-015`** — the `modify` attack's `modifyZero` is `fnNoChange` now,
  not a zero amount, and `refModifyOld` names `fnTakeAndBump`.
* **`E4-SEM-CE-016`** — a memo hit is described by what does *not* move (count,
  live set, layer scopes) and what does (the context handle, the observer
  count); `Layer.fresh` builds through a private memo map rather than being "a
  separate layer id".
* **`E4-SEM-CE-017`** — the release-order answers are `[6, [3, []]]` and
  `[7, [3, []]]`, and the host agreement is owed with the regeneration.
* **`E4-SEM-CE-019`** — `RESERVED` → `SEEDED`; the composition clause is lifted
  and what is left of it is `LAYER-FB-LAYER-IDENTITY`; observer counting is
  restated as the forgetful direction of the join rather than as invisibility.

## 12. Files

| file | change |
| --- | --- |
| `Effect4/Stateful/RefFamily.lean` | twelve rows, `RefFn`, the heap projection (from `0f5a46d`); this lane added the `set`-handle refusal to its header |
| `Effect4/Stateful/DeferredFamily.lean` | new in `0f5a46d`; this lane fixed `cancel_splices_the_waiter`'s axiom ceiling |
| `Effect4/Runtime/ScopeFamily.lean` | new in `0f5a46d` |
| `Effect4/Layer/LayerFamily.lean` | rewritten in `0f5a46d`; this lane added the two `Layer.build`/`memoize` refusals to its header |
| `Effect4/Context/ContextFamily.lean` | new in `0f5a46d`; this lane added the `withContext` and `mergeAll` notes |
| `harness/trace/Generate.lean` | imports the three new families (from `0f5a46d`); elaborates |
| `Effect4Test/Flow/RefsContract.lean` | re-pinned in `0f5a46d` |
| `Effect4Test/Flow/RefsAxiomReport.lean` | this lane: `RefFns`, `refStep` and the ten clauses added |
| `Effect4Test/Flow/DeferredsContract.lean` | this lane: imports the library family, 16 rows, 11 programs, the waiter-list receipts |
| `Effect4Test/Flow/DeferredsAxiomReport.lean` | this lane: the twelve library clauses added |
| `Effect4Test/Flow/LayersContract.lean` | this lane: rewritten for the memo map, 13 programs |
| `Effect4Test/Flow/LayersAxiomReport.lean` | this lane: eight clauses |
| `Effect4Test/Flow/ScopesContract.lean` | **new** |
| `Effect4Test/Flow/ScopesAxiomReport.lean` | **new** |
| `Effect4Test/Flow/ContextsContract.lean` | **new** |
| `Effect4Test/Flow/ContextsAxiomReport.lean` | **new** |
| `Effect4Test/Counterexamples/Semantics/Layers.lean` | this lane: rewritten over the memo map |
| `Effect4Test/Counterexamples/Runtime/Refs.lean` | this lane: repaired for the named-function request |
| `test/counterexamples/REGISTER.md` | this lane: four rows |
| `Effect4Test/Flow/TempProbe.lean` | staged as deleted in the working tree by the previous agent; nothing imports it, and the deletion is correct |
