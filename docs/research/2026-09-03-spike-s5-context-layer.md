# Spike S5 — the Context carrier and the Layer store

Status: design spike, 2026-09-03. Plan row `docs/research/2026-09-03-deep-plan.md:105` (S5).
Modules: `workshop/Deep/Context.lean` (1003 lines), `workshop/Deep/Layer.lean` (2006 lines).
Build: `lake build Deep.Context Deep.Layer`, green, 33 jobs, no `sorry`, no `axiom`, no
`native_decide`, no `@[implemented_by]`.

## Summary (15 lines)

1. `Context` is an insertion-ordered `List (Service U)` with a `Nodup` proof field
   (`workshop/Deep/Context.lean:180-184`), generic in a supplied `ServiceUniverse`.
2. `Requirement` is `abbrev Requirement := Row ServiceKey` — no second row carrier
   (`Context.lean:63`), as `PLAN.md:207` requires.
3. All five `Program.UsesOnly` laws are proved; all eleven `ENV-PG-CONTEXT` laws are proved;
   all eight counterexample classes run as `example`s with `ctx0` pinning the universe.
4. `ENV-KEY-INTERP` stays open on purpose: `UniverseAgreement` (`Context.lean:169`) is stated
   and never derived, and `transportAll` (`Context.lean:595`) takes the agreement as an argument.
5. `Ctx := Context ValU` (`Context.lean:703`) is the machine's `χ`; `ValU` is the constant
   universe, i.e. the `exists_carrier_collision` witness paid in full and exhibited.
6. All four `χ` hooks are discharged by `rfl`: `HooksAgree` (`Context.lean:872`),
   `interp_hooks` (`workshop/Deep/Layer.lean:1225`).
7. All sixteen `layer.*` census rows have proved theorems over program shapes and store steps.
8. `scope.scoped` and `scope.acquire-release` are proved as shapes; `scope.fork-linkage`'s
   linked names are witnessed by `#guard`, not by a theorem.
9. Twenty-nine `#guard` witnesses run: store steps, and eleven whole programs through the
   machine at fuel 512 on the sync scheduler.
10. **New finding.** `Deep.Fibers.finalizerOr` runs only the innermost of two *adjacent*
    `OnExit` program finalizers, so `scoped(build …)` never closes its scope (§7.1).
11. Four `-- SHIM:` blocks duplicate S2 store shapes because `Deep.Stores`' alphabets are
    closed inductives; the landing merges them (§6).
12. `mergeAll`'s early sibling interruption on a first failure is not modelled (§7.4).
13. `LayerId` into a declared table is not rc.112's layer-object identity and owes a refusal
    row (§7.3).
14. Five model clauses are evidence-only because rc.112 exports no API to observe them (§8).
15. Nothing in either module is blocked; every clause is proved, witnessed, or explicitly
    labelled a frontier here.

## 1. The Context carrier (M4a, M4b)

### 1.1 M4a — `Context/Requirement` and `Context/Service`

`docs/ENVIRONMENT-DAG.md` L1 order, fences `F-REQ` and `F-SVC`.

* `Requirement := Row ServiceKey` (`Context.lean:63`). An alias, so every `Row` law is a
  `Requirement` law with no restatement. `PLAN.md:207` and `ENVIRONMENT-DAG` open question 2
  are settled the same way.
* `Service U` (`Context.lean:89-93`): a `ServiceKey` and a value of `ServiceKey.Carrier U key`.
  The universe is a *supplied* parameter, in the trusted-boundary position
  `Effect4.FlowAlphabet` occupies (`Effect4/Context/Key.lean:314-332`).
* `serviceSig U` (`Context.lean:100-102`) is a derived `Effects.Signature`; `ServiceProgram`
  is the reused `Effects.Program`. No duplicate service program, as `PLAN.md:207` demands.
* `UsesOnly` (`Context.lean:111-117`) is an inductive predicate over the program tree, not a
  computed `requirements` row — `PLAN.md:207` forbids the latter for higher-order
  continuations.

### 1.2 M4b — `Context/Environment`

`docs/ENVIRONMENT-DAG.md` L2, fence `F-ENV`.

* Carrier: `structure Context (U) where entries : List (Service U); keysNodup : (entries.map
  Service.key).Nodup` (`Context.lean:180-184`). The uniqueness invariant is a proof field, in
  the `Effect4.ReasonAnnotations` style (`Effect4/Semantics/Cause.lean:28-33`), so no
  operation can build a duplicate.
* `get?` (`Context.lean:209`) is `lookup` over the entry list, transporting along the code
  equality with `ServiceKey.transport` (`Context.lean:201-206`) — never a `cast`.
* `add` (`Context.lean:376`) is JavaScript `Map.prototype.set`: an existing key keeps its
  position and takes the new value, a new key is appended (`setEntries`, `Context.lean:217`).
* `merge` (`Context.lean:387`) is right-biased, matching
  `provideContext(self, ctx) = updateContext(self, Context.merge(ctx))`
  (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:2197`).
* `mergeAll` (`Context.lean:391`) is the left fold of `Layer.ts:1600`.
* `Reference` (`Context.lean:406`) and `getRef` (`Context.lean:411`) are rc.112's
  `Context.Reference` / `fiber.getRef` (`internal/effect.ts:715-727`,
  `Scheduler.ts:269-298`).
* `interpret` (`Context.lean:417`) answers a `vis key` by `get?`; a missing key stops with
  `none` — the frontier `Context.getUnsafe` throws at (`internal/effect.ts:2134`).

**Source caveat, carried from the module header (`Context.lean:20-31`).** rc.112's
`Context.ts` and `Result.ts` are *not* in `vendor/effect-4.0.0-rc.112/src/`. The `Context`
model is read off its uses in `internal/effect.ts` and `Layer.ts`. Two places where the model
had to choose are documented in the module: the `Map.set` position of an existing key, and
data equality rather than object identity in `updateContext`'s `prevContext === nextContext`
test (`internal/effect.ts:2090`, modelled at `Layer.lean:929`).

### 1.3 The machine's `χ` hooks

`Deep.Fibers`' `RunInterp` declares four context hooks (`workshop/Deep/Fibers.lean:429-435`).
All four are instantiated and all four agree by `rfl`.

| `RunInterp` field | rc.112 | value in the model | discharged at |
| --- | --- | --- | --- |
| `ambientScope` | `forkScoped`, `internal/effect.ts:5400-5406` | `Env.ambientScope` (`Context.lean:788`), the `Scope` service read as a scope handle | `Layer.lean:1208`, `interp_hooks` `Layer.lean:1225` |
| `budgetOf` | `setContext`'s cached reads, `internal/effect.ts:726-727` | `Env.budgetOf` (`Context.lean:792`), with rc.112's defaults `2048` / `false` (`Scheduler.ts:271`, `:297`) | `Layer.lean:1209`, `interp_hooks` |
| `emptyContext` | `Context.empty()`, `internal/effect.ts:627` | `Context.empty` (`Context.lean:197`) | `Layer.lean:1210`, `interp_hooks` |
| `contextValue` | `getContext`, `internal/effect.ts:2153` | `encode` (`Context.lean:801`), the entry spine as a `Val` | `Layer.lean:1211`, `interp_hooks` |

The round trip `decode (encode c) = some c` is `Context.lean:823` (`decode_encode`), and it is
what every context-reading continuation of `Deep.Layer` rewrites by. The empty context's hooks
are rc.112's defaults (`hooks_empty`, `Context.lean:830`), and `scoped`'s install is what
`ambientScope` reads back (`ambientScope_add_scope`, `Context.lean:835`).

`Val` spells a context as a `ctxNil`/`ctxCons` spine rather than holding a `List`, because a
`List` field would make `Val` a nested inductive whose `DecidableEq` handler refuses
(`Context.lean:632-635`); an opaque handle would break `provideContext(context())`'s round
trip.

## 2. Clause table

State legend: **proved** = a theorem in the module, closed; **witnessed** = a `#guard` that
runs, no theorem; **frontier** = stated and true of the model, but the *run* diverges from
rc.112 for a reason named in §7.

### 2.1 The sixteen `layer.*` census rows

Row ids from `generated/effect-runtime-census.tsv:139-154`; current dispositions from
`Effect4Test/Audit/RuntimeCoverage.lean:3387-3402`, every one of which is
`disposition := "separateCalculus", coverage := "absent", witnesses := []` today.

| census id | rc.112 | theorem(s) in `workshop/Deep/Layer.lean` | state |
| --- | --- | --- | --- |
| `layer.from-build-unsafe` | `Layer.ts:289-298` | `fromBuildUnsafe_atom` `:1242`, `fromBuildUnsafe_no_scope` `:1249` | proved |
| `layer.from-build-child-scope` | `Layer.ts:333-345` | `fromBuild_forks_child` `:1257`, `scopeFork_links` `:1267`, `fromBuild_frame` `:1278`, `fromBuild_closes_on_failure` `:1285`, `fromBuild_keeps_on_success` `:1291` | proved |
| `layer.build-with-memo-map-service` | `Layer.ts:756-765` | `buildWithMemoMap_provides` `:1298`, `buildWithMemoMap_installs` `:1306`, `updateContext_sets_and_restores` `:1317`, `updateContext_restore_frame` `:1328`, `buildWithMemoMap_adds_to_result` `:1336` | proved |
| `layer.memo-build-once` | `Layer.ts:390-419` | `memoBuild_allocates` `:1352`, `memoBuild_entry` `:1363`, `memoBuild_registers_on_caller` `:1372`, `memoBuild_builds_into_layer_scope` `:1380`, `memoBuild_onExit` `:1388`, `MemoWorld.get_hit` `:1401` | proved |
| `layer.memo-finalizer-last-observer` | `Layer.ts:401-410` | `memoEntry_finalizer` `:1409`, `memoRelease_decrements` `:1417`, `memoRelease_last` `:1428`, `closeIfLast_arms` `:1436` | proved |
| `layer.memo-reuse-observer-count` | `Layer.ts:241-250` | `memoGet_hit` `:1444`, `memoize_hit` `:1454`, `memoGet_rebuilds_nothing` `:1462` | proved |
| `layer.memo-map-parent-lookup` | `Layer.ts:434-443` | `MemoWorld.get_parent` `:1475`, `MemoWorld.get_hit` `:1401` | proved |
| `layer.memo-get-or-else` | `Layer.ts:445-457` | `getOrElseMemoize_shape` `:1485` (four conjuncts) | proved |
| `layer.current-memo-map-fork-or-create` | `Layer.ts:585-588` | `forkOrCreate` `:1500` | proved |
| `layer.build-uses-ambient-scope` | `Layer.ts:800-809` | `build_uses_ambient_scope` `:1516` | proved |
| `layer.build-with-scope-still-forks-memo` | `Layer.ts:970-980` | `buildWithScope_forks_memo` `:1535` | proved |
| `layer.merge-parallel-scopes` | `Layer.ts:1587-1602` | `mergeAll_scopes` `:1548` (six conjuncts), `mergeExitContexts_success` `:1575` | proved; §7.4 records the one unmodelled clause |
| `layer.provide-dependency-first` | `Layer.ts:1907-1926` | `provide_dependency_first` `:1584` (five conjuncts) | proved |
| `layer.fresh-drops-memoization` | `Layer.ts:3850-3851` | `fresh_drops_memoization` `:1617` | proved |
| `layer.launch-holds-scope` | `Layer.ts:3897-3898` | `launch_holds_scope` `:1631` | proved |
| `layer.provide-effect-scope` | `internal/layer.ts:8-22` | `provideLayer_scope` `:1643` (six conjuncts) | proved |

### 2.2 The three scope rows S5 owes

Census rows at `generated/effect-runtime-census.tsv:75-77`; today's partial coverage and the
recorded missing clauses at `Effect4Test/Audit/RuntimeCoverage.lean:3097-3134`.

| census id | recorded missing clause today | theorem / witness | state |
| --- | --- | --- | --- |
| `scope.fork-linkage` | "that the linked names are `scopeClose(child, exit)` and `scopeRemoveFinalizerUnsafe(parent, key)` needs a scope store" (`RuntimeCoverage.lean:3098`) | `scopeFork_links` `Layer.lean:1267` for the store step; the two names by `#guard` at `Layer.lean:1798` and `:1800` over `ScopeStore.forkChild` (`Layer.lean:463-471`) | store step **proved**, names **witnessed** — no theorem names them |
| `scope.scoped` | "installs a fresh scope in the fiber context" and "restoring the previous context first" (`RuntimeCoverage.lean:3109`) | `scoped_installs_and_restores` `Layer.lean:1676` (seven conjuncts, including `ambientScope (prev.addV scopeKey …) = some scope`) | **proved** as a program shape; the *run* is a **frontier**, §7.1 |
| `scope.acquire-release` | "with the captured context needs a Context carrier" (`RuntimeCoverage.lean:3125`) | `acquireRelease_captured_context` `Layer.lean:1701` (seven conjuncts) | proved |

### 2.3 The five `Program.UsesOnly` laws (`PLAN.md:207`)

| law | theorem | state |
| --- | --- | --- |
| pure | `usesOnly_pure` `Context.lean:124` | proved |
| visit | `usesOnly_visit` `Context.lean:130` | proved |
| perform | `usesOnly_perform` `Context.lean:137` | proved |
| bind by union | `usesOnly_bind_union` `Context.lean:150` | proved |
| weakening | `usesOnly_weaken` `Context.lean:142` | proved |

### 2.4 The eleven `ENV-PG-CONTEXT` laws (`PLAN.md:208`)

| # | law | theorem | state |
| --- | --- | --- | --- |
| 1 | pointwise extensionality | `ext_keysRow` `Context.lean:430`, `equiv_iff` `:441` | proved |
| 2 | lookup at the same key | `get?_add_same` `Context.lean:447` | proved |
| 3 | lookup at a distinct key | `get?_add_other` `Context.lean:452` | proved |
| 4 | merge associativity | `merge_assoc` `Context.lean:490` | proved **pointwise** (`Equiv`); the data-level equality is true but unproved and is declared so at `Context.lean:487-489` |
| 5 | merge identities | `merge_empty_left` `Context.lean:495` (pointwise), `merge_empty_right` `:501` (data, `rfl`) | proved |
| 6 | shadowing | `merge_shadows` `Context.lean:504`, `add_add_same` `:510` | proved |
| 7 | satisfaction, empty | `satisfies_empty` `Context.lean:520` | proved |
| 8 | satisfaction, singleton | `satisfies_single` `Context.lean:524` | proved (iff) |
| 9 | satisfaction, union | `satisfies_union` `Context.lean:535` | proved (iff) |
| 10 | weakening | `satisfies_weaken` `Context.lean:547` | proved |
| 11 | handler agreement and total interpretation | `interpret_agree` `Context.lean:553` (11a), `interpret_total` `Context.lean:568` (11b) | proved |

Supporting lookup/`set` algebra: `Context.lean:224-371` (fifteen theorems), all proved.
`ENV-KEY-INTERP` is named, not closed: `UniverseAgreement` (`Context.lean:169`) is stated,
no declaration of either module proves an instance or consumes one, and `transportAll`
(`Context.lean:595`) takes the agreement as an explicit parameter
(`docs/ENVIRONMENT-DAG.md:23-25`, `Effect4/Context/Key.lean:35-38`).

### 2.5 The eight counterexample classes (`PLAN.md:208`, plus one)

All executable, all at `ValU` with `ctx0 : Ctx` (`Context.lean:888`) pinning the universe —
this is the previous agent's last unfinished note, and it is done.

| class | site | how |
| --- | --- | --- |
| nominal collision | `Context.lean:896`, `:898` | `decide` |
| carrier collision | `Context.lean:908`, `:911` | reused `ServiceUniverse.exists_carrier_collision`, then `decide` |
| mixed universes | `Context.lean:916` (`nat_ne_bool`), `:928` | proof |
| missing lookups | `Context.lean:933`, `:935` | `rfl` |
| right-biased noncommutativity | `Context.lean:940`, `:947` | `decide` |
| hidden defaults | `Context.lean:954` | `rfl` |
| proof-free casts | `Context.lean:960` | `rfl`; no `cast` of a service value appears in either module |
| **order is not observable** (the eighth, added) | `Context.lean:970` | proof: `Equiv orderAB orderBA ∧ orderAB ≠ orderBA` |

Separation gates at this instantiation: `Context.lean:999-1001`
(`DecidableEq Val`, `DecidableEq Ctx`, `DecidableEq ContextUpdate`), per
`docs/FRAMES-DAG.md` separation 4.

## 3. The Layer store

Everything the S5 brief named is declared and used:

| brief item | declaration |
| --- | --- |
| `LayerId` | `Layer.lean:51` |
| `CombineMode` | `Layer.lean:67` |
| `LayerDesc` with `mergeAll : List LayerId` | `Layer.lean:90-103` (plan §5 decision 2) |
| `MemoMapId` | `Layer.lean:57` |
| `MemoEntry` | `Layer.lean:482-493` |
| `MemoMap` with parent | `Layer.lean:496-500` |
| `MemoWorld` | `Layer.lean:503` |
| `memoGet` | `SyncOp.memoGet` `Layer.lean:156`, step `:662-667` |
| `memoReuse` | folded into `memoGet`'s observer bump, `Layer.lean:666` (`Layer.ts:245`) |
| `memoMapBuild` | `memoBuildProgram` `Layer.lean:750`, `SyncOp.memoBuild` step `:668-679` |
| `getOrElseMemoize` | `getOrElseMemoizeProgram` `Layer.lean:743` |
| `forkOrCreate` | `currentMemoMapOf` `Layer.lean:629` + `SyncOp.memoFork` `:659` |
| `build` | `ProgName.build` `Layer.lean:201`, `buildFromContextK` `:962` |
| `buildWithMemoMap` | `buildWithMemoMapProgram` `Layer.lean:738` |
| `buildWithScope` | `buildWithScopeFromContextK` `Layer.lean:969` |
| `fromBuild` | `layerBuildProgram`'s wrapper arm `Layer.lean:792`, `Name.fromBuildThen` `:1087` |
| `fromBuildUnsafe` | `constructionProgram` `Layer.lean:756` |
| `provide` | `LayerDesc.provideWith` + `provideThenK` `Layer.lean:982` |
| `merge` / `mergeAll` | `mergeAllEffectProgram` `Layer.lean:776`, `mergeForkAll` `:768` |
| `fresh` | `layerBuildProgram`'s `fresh` arm `Layer.lean:789`, `Name.freshThen` `:1091` |
| `launch` | `progOf`'s `launch` arm `Layer.lean:902` |
| `provideEffect` | `ProgName.provideLayer` `Layer.lean:215`, `Name.provideLayerWith` `:1107` |

The one instantiation of the machine's alphabets over `χ := Ctx` is `interp`
(`Layer.lean:1151-1222`); `HooksAgree` holds by `rfl` (`Layer.lean:1225`).

## 4. Witnesses, and what they answer

Twenty-nine `#guard`s, all passing under `lake build Deep.Layer`. Fuel 512, root over
`Context.empty`, store `St.empty` (or `St.seeded` for the store steps), sync scheduler via
`Deep.Fibers.runSyncExit` (`workshop/Deep/Fibers.lean:1205`).

### 4.1 Store witnesses (`Layer.lean:1755-1806`)

| witness | result |
| --- | --- |
| `memoCensus St.seeded` | `[]` |
| `memoBuild ⟨0⟩ ⟨1⟩` then `memoGet ⟨0⟩ ⟨1⟩` | one entry, `[(1, 0, 2)]` — map `1`, layer `0`, **two observers** |
| one `memoRelease` | `[(1, 0, 1)]` |
| the second `memoRelease` | `[]`, and it answers `Val.scopeHandle 2`, the layer scope `memoBuild` allocated |
| `forkedScopes.entryAt 0` close order | `[FinName.closeChildScope 1]` (`internal/effect.ts:3841`) |
| `forkedScopes.entryAt 1` close order | `[FinName.detachFromParent 0 2]` (`:3842`) — the shared key is `2` |
| forked memo map lookup of layer `0` from map `3` | `some 1`, i.e. the hit is owned by the **parent** map |
| lookup from an undeclared map `99` | `none` |

### 4.2 Machine witnesses (`Layer.lean:1808-1914`)

Table at `Layer.lean:1743-1753`. Services are reported as `(key name, value)` pairs; the
trailing `(3, 0)` is `CurrentMemoMap` added to the produced context by `Layer.ts:762`, which
is exactly the extra service §8's `Layer.memoize` note predicts.

| witness | program | result |
| --- | --- | --- |
| W1 | `scoped(build atom)` | success, `[(10, 1), (3, 0)]`, memo world empty (an atom is not memoized) |
| W2 | `build atom` with no ambient `Scope` | **failure**, and by a *defect* — `Layer.ts:807` through `internal/effect.ts:670-674`, never a typed error |
| W3 | `scoped(build (mergeAll [1, 1]))` | success, `[(10, 1), (3, 0)]`, memo `[(1, 1, 2)]` — **one construction, two observers** |
| W4 | `scoped(build (mergeAll [1, 2]))` | success, `[(10, 1), (11, 2), (3, 0)]` — both services merged |
| W5 | `scoped(build (provideWith 8 1 provide))` | success, `[(11, 1), (3, 0)]` — the dependency built first, its `keyA` reached the dependent, and `provide`'s combiner dropped it |
| W6 | `provide(layer 1, local)(service keyA)` | `Exit.success (Val.nat 1)`, memo `[(1, 1, 1)]` |
| W7 | `scoped(build (failWith))` | failure |
| W8 | `scoped(build (fresh 1))` | success; memo `[(2, 1, 1)]` and maps `[(1, none, 0), (2, none, 1)]` — **the caller's map `1` is empty and the private map `2` holds the entry** |
| W9 | `scoped(build (childScope 1))` | success, `[(10, 1), (3, 0)]` |
| W10 | `scoped(acquireRelease (value 5) 3 false)` | `Exit.success (Val.nat 5)` |
| W11 | `launch atom` | `Exit.failure (Cause.die Defect.asyncFiber)` — `never` parks, the root survives the flush, and `runSyncExit` reports rc.112's `AsyncFiberError` (`internal/effect.ts:5500-5530`) |

### 4.3 Frontier witnesses (`Layer.lean:1916-1959`)

These pin §7.1's defect so the landing has a regression test.

| witness | result |
| --- | --- |
| `witnessScopes (scoped (value 7))` | `[(0, true)]` — closed |
| `finProgCount (scoped (value 7))` | `1` |
| `witnessScopes (scoped (scoped (value 7)))` | `[(0, false), (1, true)]` — **the outer scope is not closed** |
| `finProgCount (scoped (scoped (value 7)))` | `1`, not `2` |
| `witnessScopes (scoped (seq (scoped (value 1)) (value 7)))` | `[(0, true), (1, true)]` — separated by a continuation frame, both close |
| `witnessScopes w1`, `finProgCount w1` | `[(0, false)]`, `1` |
| `witnessScopes w10` | `[(0, false)]` |

## 5. The forgetful join to `Effect4/Layer/LayerFamily.lean`

`Layer.lean:1962-2003`. `LayerFamily` is the *traced* face of the same machinery, and its own
docstring already rules that the join is forgetful, not a refusal
(`Effect4/Layer/LayerFamily.lean:36-54`). The projection carries identity, layer scope and
observer count and forgets the Deferred, the layer scope's finalizer list, and the program an
entry's `effect` is.

| declaration | statement |
| --- | --- |
| `forgetEntry` `Layer.lean:1977` | a `Deep` `MemoEntry` as `Effect4.LayerFamily.MemoEntry` |
| `forgetMap` `Layer.lean:1982` | a `Deep` `MemoMap` as `Effect4.LayerFamily.MemoMap` |
| `forget_observers` `Layer.lean:1987` | `memoGet`'s bump and the family's `bumpObservers` agree — `layer.memo-reuse-observer-count` |
| `forget_layerScope` `Layer.lean:1992` | `Layers.scopeOf` reads the scope `memoMapBuild` allocated |
| `forget_parent` `Layer.lean:1997` | the family's `memoChain` walks this model's parent — `layer.memo-map-parent-lookup` |
| `forget_fresh` `Layer.lean:2000` | a fresh map is parentless and empty on both sides — `layer.fresh-drops-memoization` |

What the join does **not** claim: the family mints a constructed-service handle
(`LayerFamily.MemoEntry.service`) that this model does not have, so `forgetEntry` takes it as
an argument. There is no map in the other direction and there cannot be one.

## 6. Every `-- SHIM:` line, and what replaces it

Cause, recorded at `Layer.lean:14-20`: the S2 alphabets in `workshop/Deep/Stores.lean` are
closed inductives with derived `DecidableEq`. A memo-entry finalizer name, a memo operation, a
context-carrying action and a context spine cannot be added to them from outside, and this
spike may not edit `Stores.lean`.

| shim | line | duplicated shape | replaced at the landing by |
| --- | --- | --- | --- |
| 1 | `Layer.lean:364` | `DeferredCell`, `DeferredStore`, and its five operations (`Layer.lean:366-424`) | `Deep.Stores.DeferredStore`, re-declared here only at this `Program`. Landing keeps one, parameterised over the program carrier. |
| 2 | `Layer.lean:428` | `ScopeEntry`, `ScopeStore` and its five operations (`Layer.lean:431-477`) | `Deep.Stores.ScopeStore`. `Effect4.Scope` itself is reused unchanged in both. Landing keeps one, parameterised over `φ := FinName`. |
| 3 | `Layer.lean:831` | `closeSeqChain` | `Deep.Stores.closeSeqChain` |
| 4 | `Layer.lean:840` | `closeParChain` | `Deep.Stores.closeParChain` |
| 5 | `Layer.lean:852` | `closeScopeProgram` | `Deep.Stores.storesCloseScope` |

The exact change: make `Deep.Stores`' `FinName` / `SyncOp` / `Name` / `ProgName` the alphabets
this module declares (`Layer.lean:113-332`), or make `Deep.Stores` a functor over them; then
delete `Layer.lean:362-477` and `:830-864` and import.

## 7. What the machine or the stores lack

### 7.1 `Deep.Fibers.finalizerOr` drops the outer of two adjacent `OnExit` program finalizers

**This is new in S5 and it is a defect, not a modelling choice.**

`workshop/Deep/Fibers.lean:776-787` takes the program-finalizer path only when
`f.frame.stack`'s **immediate head** is `Prim.onExit`:

```
    match f.frame.stack with
    | (Prim.onExit body fin flag) :: rest =>
      match interp.finalizerProgram fin exit with
      | some program => …
      | none => stepFrame interp m f yielding
    | _ => stepFrame interp m f yielding
```

The frame machine's delivery does not use the head: `resumeValue` calls
`getCont Arm.contA false` (`Effect4/Runtime/Runtime.lean:2300`), which **skips** every frame
that does not declare `contA`. An `onExit`'s `ensure` pushes exactly such a mask-restoring
frame (`Effect4/Runtime/Runtime.lean:697-703`, `ensure_onExit_masks`). So when an inner
`OnExit` finishes and re-raises its exit, the *next* `OnExit` is reached by a skip rather than
being the head, `finalizerOr` falls through, and the frame machine answers it with the pure
shortcut `armA` (`Runtime.lean:839`, through `interp.finalizerExit`, which this interp sets to
`fun _ _ => Exit.void`, `Layer.lean:1158`). The outer finalizer program never runs, and no
event records that it did not.

Measured: `finProgCount (scoped (scoped (value 7))) = 1` (`Layer.lean:1949`), and the outer
scope stays open (`Layer.lean:1947`).

Why it matters here rather than in S1/S3: *every* `Layer` build sits under `updateContext`'s
restoring frame (`internal/effect.ts:2092-2095`), and `scoped` pushes its own
(`internal/effect.ts:3943-3946`). The two are adjacent in every `scoped(build …)`. rc.112 runs
both; the model runs one.

**Exact change** (out of this spike's fence, `workshop/Deep/Fibers.lean` is not editable
here): `finalizerOr` must consult the frame the exit will actually be delivered to, not the
stack head — i.e. perform the same `contA`/`contE` skip `getCont` performs
(`Runtime.lean:2300`, `:2334`), and take the `interp.finalizerProgram` path when that frame is
a `Prim.onExit` whose `finalizerProgram` is `some`. rc.112 lines the fix is against:
`internal/effect.ts:4021` (an `OnExit` finalizer is a program, run as one), with
`:2092-2095` and `:3943-3946` as the two adjacent frames.

Consequence for the table: `scope.scoped`'s *shape* clause (`scoped_installs_and_restores`,
`Layer.lean:1676`) is proved and correct — the machine will run the right program. What is a
frontier is the machine's delivery of it.

### 7.2 The interp's unused arms are stubs, and say so

`Layer.lean:1160-1164`: `iterNext`, `loopTest`, `loopBody`, `loopStep`, `loopDone` are
constant. `Layer.ts` and `internal/layer.ts` declare no iterator and no loop primitive, so no
program of this instantiation reaches them. `parkOf := fun _ => none` (`Layer.lean:1167`):
this alphabet has no `join`/`await` primitive; `awaitAll` is a `withFiber` action instead
(`Layer.lean:340`). `stackAnnotations := fun _ => ReasonAnnotations.empty`
(`Layer.lean:1221`), matching the module header's note that this instantiation contributes no
annotations (`Context.lean:628-629`).

### 7.3 `LayerId` is not rc.112's layer identity

rc.112 keys the memo `Map` on the layer **object** (`Layer.ts:411`, `:438`). `LayerId` into a
declared `LayerTable` is the model's stand-in and owes a `LAYER-FB-LAYER-IDENTITY` refusal row
of the `SCOPE-FB-KEY-IDENTITY` shape (`Effect4/Runtime/Scope.lean:314-320`). Recorded in the
module at `Layer.lean:34-37`. Exact change: add the refusal row at the landing; no model
change makes an index into object identity.

### 7.4 `mergeAll`'s early sibling interruption is not modelled

`Layer.ts:1597-1598` is `forEach` with `concurrency: layers.length`, which interrupts the
outstanding siblings when one fails. `mergeForkAll` (`Layer.lean:768-773`) forks every layer's
build, awaits them all, and merges (`Layer.lean:1014-1020` folds the failures' reasons into
one cause). Exact change: `mergeForkAll` would have to interrupt the outstanding forks on the
first failing awaited exit, which needs the machine's `WithFiberAction.awaitAll` to report a
first failure rather than the full exit list — it does not
(`workshop/Deep/Fibers.lean:276-278`, `Layer.lean:1139`). Recorded at `Layer.lean:37-39`.

### 7.5 `Context.merge` associativity is pointwise only

`merge_assoc` (`Context.lean:490`) is over `Equiv`, which is what a program observes. The
data-level equality also holds — positions of existing keys are kept and new keys are appended
in operand order on both sides — and is declared unproved at `Context.lean:487-489`. Exact
change: prove it on `entries`, or record the pointwise scope as deliberate at the landing.
`merge_empty_right` is already data-level (`Context.lean:501`, by `rfl`).

### 7.6 The stores share one name counter

`St.nextName` (`Layer.lean:564`) mints scope keys, finalizer keys and memo-map ids from one
counter. rc.112 has three independent sources (a `Map` key counter per scope, a fresh object
per memo map). This is visible in the witnesses — W8's private memo map is `⟨2⟩` because the
caller's is `⟨1⟩` — and is harmless as long as no clause reads a key's numeric value. No
clause does.

### 7.7 No `Context.ts` in the vendored tree

`vendor/effect-4.0.0-rc.112/src/` has neither `Context.ts` nor `Result.ts`
(`Context.lean:20-22`). Every `Context` operation is transcribed from its *uses*. The two
model choices this forces are listed in §1.2. Exact change: vendor `Context.ts` at the pin, or
keep the choices as declared model rulings.

## 8. What rc.112 has no public API for — evidence-only clauses

From `docs/research/2026-09-03-lowering-l2-host-tails.md` §12 (`:573-631`). Each of these
makes the corresponding *host-comparable* row a refusal, so the matching model clause here is
**evidence-only**: proved of the model, not comparable against a host trace at this pin.

| §12 item | rc.112 | S5 clause it makes evidence-only |
| --- | --- | --- |
| 12.1 the children set (`childrenSnapshot`, `awaitChildren`) | `_children` is `internal/effect.ts:534`, accessor `:703-705`, populated only for a non-daemon fork `:5279-5282`; `Fiber.ts:70-92` exposes neither, and `./internal/*` maps to `null` in `exports`. Only fused `Effect.awaitAllChildren` (`Effect.ts:17207`) is public | `mergeAll_scopes`' fork/await clause (`Layer.lean:1548`), which forks one tracked child per layer and awaits them together |
| 12.2 a layer's raw builder | `Layer.build(memoMap, scope)` is `@internal` at `Layer.ts:56` and stripped from `dist/Layer.d.ts:44-48` | `ProgName.layerBuild` and `layerBuildProgram` (`Layer.lean:207`, `:784`), and `fresh`'s one-line spelling at `Layer.ts:3851` that `fresh_drops_memoization` (`Layer.lean:1617`) transcribes |
| 12.3 `Layer.memoize` | no such export; memoization is `Layer.fromBuildMemo` (`Layer.ts:380-388`), reachable only through `buildWithMemoMap`, which adds `CurrentMemoMap` to the produced context (`:761-765`) | `LayerDesc.memoized` (`Layer.lean:93`) and `getOrElseMemoize_shape` (`Layer.lean:1485`). The extra service is *visible in the witnesses* as the trailing `(3, 0)` of §4.2 |
| 12.4 `Scope.extend` | no such export; the non-closing form is `Scope.provide` (`Scope.ts:310-387` = `internal/effect.ts:3932-3936`), the closing one `Scope.use` (`:616-661` = `:3950-3959`) | `FinName.closeScopeWith` (`Layer.lean:128`) and `provideLayer_scope`'s `scopedWith` clause (`Layer.lean:1643`) |
| 12.5 `Effect.withContext` | no such export; the reader is `Effect.contextWith` (`Effect.ts:11346` = `internal/effect.ts:2156-2158`) and `Effect.context()` (`:2152`) | `ProgName.getContext` / `ActionName.getContext` (`Layer.lean:177`, `:342`) and every `contAOf` arm that rewrites `decode (encode ctx)`; also `acquireRelease`'s `contextWith` capture, `acquireRelease_captured_context` (`Layer.lean:1701`) |

## 9. `sorry` inventory

None. `Select-String` over `workshop/Deep/Context.lean` and `workshop/Deep/Layer.lean` for
`\bsorry\b`, `^axiom `, `native_decide` and `@[implemented_by]` returns nothing. Every clause
theorem closes by `rfl`, `decide`, `simp only [...]` on a hypothesis, or structural induction.
Both modules set `autoImplicit false`.

## 10. What the landing owes from S5

1. Fix `finalizerOr` (§7.1) and re-run the frontier `#guard`s at `Layer.lean:1943-1959`; three
   of them are expected to flip once the fix lands.
2. Merge the five shims into `Deep.Stores` (§6).
3. Add the `LAYER-FB-LAYER-IDENTITY` refusal row (§7.3).
4. Re-dispose the sixteen `layer.*` rows of `Effect4Test/Audit/RuntimeCoverage.lean:3387-3402`
   from `absent` with the theorems of §2.1 as witnesses, and close the recorded missing clauses
   of `scope.fork-linkage`, `scope.scoped` and `scope.acquire-release`
   (`RuntimeCoverage.lean:3098`, `:3109`, `:3125`) with §2.2's theorems.
5. Label the five §8 clauses evidence-only wherever a host comparison is claimed.
6. Decide §7.5 (data-level `merge` associativity: prove or declare).
</content>
</invoke>
