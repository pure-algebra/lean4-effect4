# Lowering lane L2: the host tails over rc.112

Lane report, 2026-09-03. Pin `effect@4.0.0-rc.112`, upstream
`2600f62f4532026928454dcea8d1c48557b3f942`. TypeScript only; no `Effect4/`,
`Effect4Test/`, `workshop/`, `generated/`, `lakefile.toml` or
`harness/trace/Generate.lean` was touched, and no `lake` command was run.

## Summary

* **The toolchain is installed and every pin matches.** `EFFECT4_EFFECT_NODE_MODULES`
  was unset and neither Foldlab path existed, so a fresh installation was made at
  `C:\Users\kokok\Dev\effect4-host\`, outside the repository. All three package
  integrity hashes equal `PORT-MANIFEST.md`'s, the package tree hashes to
  `host-pin.json`'s `aea8ac8a…` over exactly 2,341 files, `src/Schema.ts` hashes
  to the installed-bytes digest the manifest records, and all thirteen vendored
  `src/` files are byte-equal to the installed ones. §1.
* **Six tails carry the whole surface.** A new `fibers-tail.ts` implements the
  twelve-row fiber profile; a new `context-tail.ts` implements `Context`; and
  `ref-tail.ts`, `deferred-tail.ts`, `scope-tail.ts` and `layer-tail.ts` each
  gain a full-surface service beside the narrow one whose goldens are pinned.
  **Eighty rows across six services** — 12 fiber, 13 ref, 15 deferred, 12
  scope, 15 layer, 13 context. Seventy-six are an rc.112 call cited by line;
  the other four (`ran`, `exitsSeen`, `provideCount`, `referenceDefault`) are
  probes that report what the run observed. §3-§8.
* **Both gates are clean.** `tsc --noEmit` at `typescript@7.0.2` over 30 files:
  0 errors. `@effect/tsgo@0.38.0` diagnostics, `--strict`, over the same 30:
  `0 errors, 0 warnings and 0 messages`, Effect v4 detected in every file. §9.
* **Sixty programs run** under `node --experimental-strip-types`, with no tracer
  defect. **All 34 pre-existing goldens still match byte for byte**, so nothing
  already pinned changed. §10.
* **Six stubs**, all named `*-fixture.stub.ts` and all marked
  `// STUB: replaced by the generated fixture`. §11.
* **Five things rc.112 has no public API for**, each of which makes the
  corresponding Lean row a refusal rather than a claim: the children-set pair,
  `Layer`'s raw builder, `Layer.memoize`, `Scope.extend`, and
  `Effect.withContext`. Two spellings of `fork-lowering.md` §(c) are simply
  wrong against rc.112 and are corrected here. §12.

---

## 1. The toolchain

### 1.1 What was absent

| Probe | Result |
| --- | --- |
| `$env:EFFECT4_EFFECT_NODE_MODULES` | unset |
| `C:\Users\kokok\Dev\foldlab\library\effects\node_modules` | absent |
| `$HOME\Dev\foldlab\library\effects\node_modules` | absent (same path) |

Node 22.23.2 and npm 10.9.8 are on `PATH` via mise.

### 1.2 What was installed

`C:\Users\kokok\Dev\effect4-host\package.json`, outside the repository, pinning
the three exact versions; `npm install` there added 12 packages in 34s.
`EFFECT4_EFFECT_NODE_MODULES` was **not** written into any repository file; it
is only the argument the check scripts below take.

### 1.3 Integrity, item by item

`C:\Users\kokok\Dev\effect4-host\l2-pin-check.mjs` runs the same walk
`scripts/check-fiber-supervision-host.sh` runs (`file\0sha256(bytes)\n` records
over the sorted relative paths, hashed). Every line MATCHED:

| Fact | Actual | Expected, and from where |
| --- | --- | --- |
| `effect` version | `4.0.0-rc.112` | `harness/trace/host-pin.json` |
| `typescript` version | `7.0.2` | same |
| `@effect/tsgo` version | `0.38.0` | same |
| `effect` file count | 2341 | same |
| `effect` package-tree SHA-256 | `aea8ac8a25b17aa82796fad7acc1371bc9a92bbd7d25ce24f2598016f9920aad` | same |
| package symlinks | 0 | the gate refuses any |
| `src/internal/effect.ts` | byte-equal to `vendor/effect-4.0.0-rc.112/src/internal/effect.ts` | the gate's own comparison |
| all 13 vendored `src/` files | byte-equal to the installed `src/` | this lane, additionally |
| installed `src/Schema.ts` SHA-256 | `9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784` | `PORT-MANIFEST.md`, "installed `Schema.ts`" |

npm's own lockfile integrity, against `PORT-MANIFEST.md`'s "Authority pins":

| Package | `package-lock.json` integrity | Manifest |
| --- | --- | --- |
| `effect` | `sha512-wXxwuh1Ywnv4cPRM3Wfa0vDwuOHnZ1TsTgHJkG9XgzND6inhBH9n1vBxhg3iIXOia/OrpmvVmd3lrD4vq6bF3A==` | identical |
| `typescript` | `sha512-8FYau96o3NKOhbjKi/qNvG/W5jhzxkbdm5sj9AbZ/5T5sWqn3hJgLfGx27sRKZWTvyzCP8dLRBTf5tBTSRVUNA==` | identical |
| `@effect/tsgo` | `sha512-eazN0kX+WNT1jNjIm/l5esnkpKVfd1wNh2ig0pfaULKuI2PZh0JwjbepDPUr6MWx5cqOiUgwStNf5hGhg2w00g==` | identical |

**Nothing did not match.** Two things are recorded as *additions* rather than
matches:

* `@types/node@26.4.1` was installed as a dev dependency. It is outside the
  three-package pin and is needed only because `harness/trace/tsconfig.json`
  names `"types": ["node"]`. It contributes no runtime value; the tails declare
  their own `declare const process`.
* On Windows the pinned compiler ships as
  `node_modules/@typescript/typescript-win32-x64/lib/tsc.exe`, not as the
  `lib/tsc.original` that `scripts/check-lowering-types.sh` and
  `scripts/check-fiber-supervision-host.sh` `find` for. Those two gates cannot
  locate a compiler on this platform as written; this lane invoked
  `node_modules/.bin/tsc` (which reports `Version 7.0.2`) instead. That is a
  portability gap in the gates, not in the pin.

### 1.4 Reproducing the checks

Three scripts, all outside the repository:

| Script | What it does |
| --- | --- |
| `C:\Users\kokok\Dev\effect4-host\l2-pin-check.mjs` | the integrity table of §1.3 |
| `C:\Users\kokok\Dev\effect4-host\l2-typecheck.ps1` | copies `harness/trace/*.ts` + `tsconfig.json` into `l2-check/`, junctions `node_modules`, extends `files` with this lane's additions, runs `tsc --noEmit` |
| `C:\Users\kokok\Dev\effect4-host\l2-goldens.ps1` | replays every golden under `generated/traces/{ref,deferred,scope,layer,fiber}` against the edited tails and diffs the rows |

`l2-typecheck.ps1` is the same shape as `scripts/check-lowering-types.sh`: a
scratch copy with a linked `node_modules`, so the repo's own
`harness/trace/tsconfig.json` `files` list is **not changed by this lane**.
Adding the seven new modules to it is the landing step for whoever routes these
tails into `scripts/check-trace-host.sh`.

---

## 2. What this lane added and changed

| File | Change |
| --- | --- |
| `harness/trace/fibers-tail.ts` | **new** — the twelve-row fiber profile |
| `harness/trace/fibers-fixture.stub.ts` | **new** — stub |
| `harness/trace/context-tail.ts` | **new** — the `Context` surface |
| `harness/trace/context-fixture.stub.ts` | **new** — stub |
| `harness/trace/ref-tail.ts` | the `MutableRef` handle brand, `fullLive` (13 rows), 5 programs |
| `harness/trace/refs-fixture.stub.ts` | **new** — stub |
| `harness/trace/deferred-tail.ts` | `fullLive` (15 rows), 5 programs |
| `harness/trace/deferreds-fixture.stub.ts` | **new** — stub |
| `harness/trace/scope-tail.ts` | the `Fiber` handle brand, `fullLive` (12 rows), 4 programs, `stallMs` |
| `harness/trace/scopes-fixture.stub.ts` | **new** — stub |
| `harness/trace/layer-tail.ts` | `fullLive` (15 rows), 7 programs, `stallMs` |
| `harness/trace/layers-fixture.stub.ts` | **new** — stub |

**No operation that an existing tail already implemented changed behaviour.**
The narrow services (`Refs`, `ERefs`, `Deferreds`, `Scopes`, `Layers`,
`Fibers` of `fiber-fixture.ts`) are untouched, and §10 shows all 34 of their
goldens still match. The two handle brands added are disjunctions, and the
objects they brand (`MutableRef`, `Fiber`) are only ever wired by the *new*
rows, so the narrow rows' handle indices are unchanged — which §10 confirms
rather than assumes.

---

## 3. `fibers-tail.ts` — the fiber profile

Twelve rows, the spellings of `docs/research/2026-09-03-spike-s3-fork-flow.md`
§2 and `docs/research/2026-09-03-lowering-l1-fiber-profile.md` §1, which landed
in `Effect4/Target/TypeScript/FiberProfile.lean` while this lane ran and agrees
with this tail on every name, every request and every answer.

| Row | rc.112 call | `vendor/effect-4.0.0-rc.112/src/` |
| --- | --- | --- |
| `fork(root, args, daemon, region)` | `Effect.forkIn` when `region` is `some`; `Effect.forkDetach` when `daemon`; `Effect.forkChild` otherwise — all through `forkUnsafe` | `Effect.ts:17033` / `:17168` / `:16990`; `internal/effect.ts:5337-5379`, `:5287-5311`, `:5228-5261`, `:5264-5284` |
| `forkScoped(root, args, daemon, region)` | `Effect.forkScoped` = `flatMap(scope, forkIn)` | `Effect.ts:17128`; `internal/effect.ts:5400-5406` |
| `join(fiber)` | `Fiber.join` | `Fiber.ts:279`; `internal/effect.ts:814-856` |
| `awaitFiber(fiber)` | `Fiber.await` + `Exit.isSuccess` / `Exit.findErrorOption` | `Fiber.ts:161-198`; `internal/effect.ts:767-778`; `Exit.ts:393`, `:1283` |
| `interruptFiber(fiber)` | `Fiber.interrupt` | `Fiber.ts:354`; `internal/effect.ts:857-861` |
| `interruptAll(fibers)` | `Fiber.interruptAll` | `Fiber.ts:527`; `internal/effect.ts:888-901` |
| `childrenSnapshot` | `Effect.withFiber` + the tracked set — **refusal**, §12.1 | `Effect.ts:2392`; `internal/effect.ts:534`, `:703-705`, `:5314-5334` |
| `awaitChildren(snapshot)` | `Fiber.awaitAll` over the children added since — **refusal**, §12.1 | `Fiber.ts:235`; `internal/effect.ts:779-813`, `:5322-5331` |
| `raceAll(entrants)` | `Effect.raceAll` over the root table | `Effect.ts:8760`; `internal/effect.ts:1477-1534` |
| `uninterruptibleIn(root, args)` | `Effect.uninterruptible` | `Effect.ts:14306`; `internal/effect.ts:4302-4310` |
| `interruptibleIn(root, args)` | `Effect.interruptible` | `Effect.ts:14199`; `internal/effect.ts:4331-4337` |
| `yieldNow(priority)` | `Effect.yieldNowWith` | `Effect.ts:2374`; `internal/effect.ts:982-994` |

Four decisions worth stating.

**The root table.** A fork's `root` field is the **block id** of a declared
root, because the L1 lane's synthetic dispatch case is
`Lowering.rootEntryBase + block` and the emitted per-root export is
`prog__root3` for the root at block 3 (L1 §3). `enter` resolves that id through
the fixture's exported `fibersRoots` map and provides the traced service to the
child; a request naming no declared root is `Effect.die`, which is
`fork-lowering.md` §(c) note 4 and the host counterpart of
`WithFiberAction.refuse`. Nothing is closed over.

**Immediacy is not a request field.** Every fork passes
`{ startImmediately: false }` (§(c) note 2), so the child is queued and nothing
of it runs. Which fiber then holds the processor is read off the golden's tape
and handed over through `TapeScheduler`'s `armed` hook in `tracer.ts`; the tail
installs **no scheduler**, exactly as `fiber-tail.ts` does not.

**`forkScoped` refuses its two unused request fields.** A `forkScoped` whose
request names a region is `ForkRefusal.scopedNamesRegion` in Lean (S3 §2), so
the host dies rather than silently ignoring the field; the same for `daemon`.
The ambient `Scope` `forkScoped` reads is a fact of the fiber's *context*, and
the tail installs one before the run.

**`awaitFiber`'s loss.** A cause with no `Fail` reason — a die, an interrupt —
has no `Val` preimage, and `exitAsValue` (`ForkFlow.lean:330-338`) reads it as
unit. The tail answers `Result.fail` carrying the *absence*, which `wire`
renders `"[]"`, rather than inventing a number. The trace row is
`answer awaitFiber [false, []]` and it is visible in §10's
`interruptAllChildren`.

Nine programs, all runnable: `forkJoin`, `forkScopedAwait`, `forkInRegion`,
`daemonSurvives`, `childrenRoundTrip`, `interruptAllChildren`, `raceAllRoots`,
`maskedRoot`, `emptyRace`.

---

## 4. `ref-tail.ts` — the full `Ref` surface

The narrow six-row `Refs` and `ERefs` are unchanged. `RefsFull` adds the
thirteen Effect-valued operations of `Ref.ts`. Every one is `Effect.sync` of a
single thunk in rc.112 — none is `suspend`, `withFiber` or a callback — so
nothing here parks.

| Row | rc.112 call | `Ref.ts` |
| --- | --- | --- |
| `make(initial)` | `Ref.make` | `:173` (with `makeUnsafe` `:142-146`) |
| `get(ref)` | `Ref.get` | `:200` |
| `set(ref, value)` | `Ref.set` | `:307`, `MutableRef.ts:1067-1070` |
| `getAndSet(ref, value)` | `Ref.getAndSet` | `:399-404` |
| `setAndGet(ref, value)` | `Ref.setAndGet` | `:747` |
| `update(ref, amount)` | `Ref.update` | `:1273-1276` |
| `getAndUpdate(ref, amount)` | `Ref.getAndUpdate` | `:496-501` |
| `updateAndGet(ref, amount)` | `Ref.updateAndGet` | `:1368` |
| `updateSome(ref, floor)` | `Ref.updateSome` | `:1502-1508` |
| `getAndUpdateSome(ref, floor)` | `Ref.getAndUpdateSome` | `:635-643` |
| `updateSomeAndGet(ref, floor)` | `Ref.updateSomeAndGet` | `:1639-1646` |
| `modify(ref, amount)` | `Ref.modify` | `:896-901` |
| `modifySome(ref, amount)` | `Ref.modifySome` | `:1159-1163` |

**`set` answers the cell, as an allocation index.** rc.112 declares `Ref.set`
as `Effect<void>`, but its thunk is an *expression* arrow over `MutableRef.set`,
which writes `current` and returns the ref itself — census
`ref.set-void-returns-cell` / `ref.cell-set-returns-self`, counterexample
`E4-SEM-CE-009`. The row's declared answer is therefore the cell, the tail
registers `~effect/MutableRef` (`MutableRef.ts:18`) as a handle brand, and the
cell reaches the wire through `wire`'s handle branch as its index in first-seen
order — the same `Handle` carrier every other opaque host object in this
harness uses. The observed contrast, from §10:

```
op  make      7        answer  make       0     -- the Ref, handle 0
op  set  [0, 9]        answer  set        1     -- the cell, handle 1
op  update  [0, 1]     answer  update    []     -- a block-bodied thunk: undefined
```

Two `void`-declared operations of one rc.112 module hand back different things,
and that is now a row rather than a footnote.

**The partial functions are names.** DB-02 forbids a Lean function in canonical
content, so `updateSome`, `getAndUpdateSome`, `updateSomeAndGet` take a `floor`
naming the partial update `c > floor ? some (c - 1) : none`, and `modifySome`
takes an `amount` naming its pair. The tail is the interp, exactly as
`PrimInterp` is (`Effect4/Runtime/Runtime.lean:191-215`). A `floor` above the
cell exercises every `None` arm at once — `partialNoRewrite` in §10 shows all
four leaving the cell at 7.

Five programs: `setAnswersCell`, `readBeforeWrite`, `writeThenAnswer`,
`partialNoRewrite`, `modifyPair`.

---

## 5. `deferred-tail.ts` — the full `Deferred` surface

The narrow seven-row `Deferreds` is unchanged. `DeferredsFull` adds the
fourteen operations of `Deferred.ts` plus a `ran` probe.

| Row | rc.112 call | `Deferred.ts` |
| --- | --- | --- |
| `make` | `Deferred.make` | `:171`, `makeUnsafe` `:140-145` |
| `isDone(cell)` | `Deferred.isDone` | `:1366`, `isDoneUnsafe` `:1382` |
| `poll(cell)` | `Deferred.poll` + `Effect.result` | `:1414-1416` |
| `succeed(cell, value)` | `Deferred.succeed` | `:1514` |
| `fail(cell, error)` | `Deferred.fail` | `:669` |
| `failCause(cell, error)` | `Deferred.failCause` + `Cause.fail` | `:877`; `Cause.ts:482` |
| `die(cell, defect)` | `Deferred.die` | `:1087` |
| `interrupt(cell)` | `Deferred.interrupt` | `:1231-1232` |
| `interruptWith(cell, fiberId)` | `Deferred.interruptWith` | `:1332-1337` |
| `complete(cell, code)` | `Deferred.complete` | `:330-335` |
| `completeWith(cell, code)` | `Deferred.completeWith` | `:456-461` |
| `done(cell, code)` | `Deferred.done` | `:570-571` |
| `into(code, cell)` | `Deferred.into` | `:1774-1784` |
| `awaitValue(cell)` | `Deferred.await` | `:173-186`; `internal/effect.ts:1163-1169` |
| `ran` | the tail's own probe over the primitive table | — |

Every completion above ends in `doneUnsafe` (`:1648-1662`), which answers
`false` and changes nothing when a completion is stored, and otherwise stores
it, **clears the waiter array before resuming**, and resumes every waiter in
registration order.

**Completions are names, not functions**, the same DB-02 discipline as Ref's
partial updates: `complete`, `completeWith`, `done` and `into` take a `code`
naming a primitive, and `ran` records which of them were actually *run*. That
turns the census contrast into two rows:

```
op completeWith [0, 4]  answer completeWith true   op ran []  answer ran []
op complete     [1, 4]  answer complete     true   op ran []  answer ran [4]
```

`completeWith` stores its primitive without running it; `complete` runs it once
through `into`. That is `deferred.complete-with-stores-effect` and
`deferred.complete-runs-once` side by side.

**A found loss.** `poll`'s declared answer is
`Option<Result<number, number>>`, and `Effect.result` — the only total reading
of a stored completion into a `Result` — catches a typed failure and **not** an
interrupt. Polling an interrupted cell therefore interrupts the reading fiber
and the row never answers: the first draft of `interruptIsAFailure` produced
`op poll 0` followed by `done {"interrupted":true}`. The tail's `poll` is
*correct* and was left exactly as it was; the fixture program reads interrupted
cells with `isDone` instead, and the loss is recorded here and in the stub. It
is the same loss `ForkFlow.lean:330-338` records for `exitAsValue`.

Five programs: `completionShapes`, `interruptIsAFailure`,
`completeWithStoresEffect`, `doneIsCompleteWith`, `intoUninterruptible`.

---

## 6. `scope-tail.ts` — the rest of the `Scope` surface

The narrow four-row `Scopes` is unchanged, `remove` included: it still has no
rc.112 entry point, because the package's `exports` map sends `./internal/*` to
`null`, and it is still performed over the public mutable `Scope.state`.

| Row | rc.112 call | source |
| --- | --- | --- |
| `make(parallel)` | `Scope.make(strategy)` | `Scope.ts:240`; `internal/effect.ts:3925-3930` |
| `makeUnsafe(parallel)` | `Scope.makeUnsafe(strategy)` | `Scope.ts:271`; `internal/effect.ts:3915-3922` |
| `fork(scope, parallel)` | `Scope.fork` | `Scope.ts:489-492`; `internal/effect.ts:3830-3844` |
| `forkUnsafe(scope, parallel)` | `Scope.forkUnsafe` | `Scope.ts:530-531`; `internal/effect.ts:3834-3844` |
| `addFinalizer(scope, key)` | `Scope.addFinalizerExit`, exit-blind reading | `Scope.ts:456` |
| `addFinalizerExit(scope, key)` | `Scope.addFinalizerExit`, exit recorded | `Scope.ts:422-423`; `internal/effect.ts:3847-3858` |
| `close(scope)` | `Scope.close` | `Scope.ts:567`; `internal/effect.ts:3775-3798`, `:3806-3827` |
| `extend(root, scope)` | `Scope.provide` — **rc.112 has no `Scope.extend`**, §12.4 | `Scope.ts:310-387`; `internal/effect.ts:3932-3936` |
| `use(root, scope)` | `Scope.use` | `Scope.ts:616-661`; `internal/effect.ts:3950-3959` |
| `forkFiberIn(root, scope)` | `Effect.forkIn` | `Effect.ts:17033`; `internal/effect.ts:5337-5379` |
| `runIn(fiber, scope)` | `Fiber.runIn` | `Fiber.ts:758-805`; `internal/effect.ts:5441-5461` |
| `exitsSeen` | the tail's own probe | — |

**Strategies are a boolean** because the wire alphabet has no string arm:
`false` is `"sequential"`, rc.112's default (`internal/effect.ts:3915`), `true`
is `"parallel"`. The two differ only in *how* `scopeCloseFinalizers` runs the
finalizers (`:3806-3827`) — sequentially through `exit()`, or as immediate
daemon forks inheriting the closing fiber's mask, awaited together.

**`extend` and `use` name a declared root**, the way a fork does, because their
argument is a program requiring `Scope` and a request cannot carry one. The
contrast the `extendKeepsOpen` golden shows is exact: after `extend` the scope
is still open and `exitsSeen` is empty; after `close` it has one entry; `use`
provides *and closes* with the body's exit, so its entry appears without a
`close`.

Four programs: `forkLinkage`, `parallelStrategy`, `extendKeepsOpen`,
`fiberLinkage`.

---

## 7. `layer-tail.ts` — the rest of the `Layer` surface

The narrow four-row `Layers` is unchanged. `LayersFull` adds fifteen rows.
**Layers and memo maps are handle indices into two tail-local tables**, because
rc.112 keys the memo `Map` on the layer *object* (`Layer.ts:411`, `:438`) and
the model's stand-in is a `LayerId` index (deep-state-models §3.3); a
`LAYER-FB-LAYER-IDENTITY` refusal row of the `SCOPE-FB-KEY-IDENTITY` shape is
owed. A built context answers as the bases it carries, read back through the
declared tags with `Context.getOption` and `Ref.getUnsafe`.

| Row | rc.112 call | `Layer.ts` |
| --- | --- | --- |
| `declare(base)` | `Layer.effect` → `effectContext` → `fromBuildMemo` | `:1347`, `:1435-1439`, `:1479-1481`, `:380-388` |
| `provide(self, that)` | `Layer.provide` = `provideWith(…, identity)` | `:2008`, `:2345-2348`, `:1907-1926` |
| `provideMerge(self, that)` | `Layer.provideMerge` | `:2436`, `:2797-2805` |
| `merge(self, that)` | `Layer.merge` | `:1705`, `:1902` |
| `mergeAll(self, that)` | `Layer.mergeAll` → `mergeAllEffect` | `:1652-1658`, `:1587-1602` |
| `fresh(layer)` | `Layer.fresh` | `:3850-3851` |
| `memoize(layer)` | `Layer.fromBuildMemo` over `Layer.buildWithMemoMap` — **refusal**, §12.2/§12.3 | `:380-388`, `:645`, `:756-765` |
| `orDie(layer)` | `Layer.orDie` | `:3327-3328` |
| `unwrap(layer)` | `Layer.unwrap` | `:1580-1585` |
| `makeMemoMap` | `Layer.makeMemoMapUnsafe` | `:492` |
| `forkMemoMap(memo)` | `Layer.forkMemoMapUnsafe` | `:511`, `MemoMapImpl.get` `:434-443` |
| `buildWithMemoMap(layer, memo)` | `Layer.buildWithMemoMap` | `:645`, `:756-765` |
| `buildWithScope(layer)` | `Layer.buildWithScope` | `:863`, `:970-980`, `:585-588` |
| `launch(layer)` | `Layer.launch` | `:3897-3898`; `internal/effect.ts:1172` |
| `provideCount(base)` | the tail's own counter | — |

**A finding the goldens make visible.** `buildWithScope` replaces only the
scope; the memo map is still `CurrentMemoMap.forkOrCreate(fiber.context)`
(`:974-979`, `:585-588`). With no ambient `CurrentMemoMap` two `buildWithScope`
calls therefore get **two different memo maps and share no memoization at all**
— census `layer.build-with-scope-still-forks-memo`, observed directly: the
first draft of `freshDropsMemoization` counted four constructions where three
were expected. Both memoization witnesses now name their memo map, and the
distinction is what `declareIdentity` pins:

```
declare 2 -> layer 4 ;  declare 2 -> layer 5     -- structurally equal
buildWithMemoMap [4, 1] ; buildWithMemoMap [4, 1] ; provideCount 2 -> 1
buildWithMemoMap [5, 1] ;                          provideCount 2 -> 2
```

Two structurally equal declarations are two memo entries in one memo map. That
is exactly why keying a Lean model on `LayerDesc` would be wrong.

`launch` never answers: it is `scoped(andThen(build(self), never))`, so the run
parks and the golden is a frontier, recorded through `RunOptions.stallMs`.

Seven programs: `provideDependencyFirst`, `mergeParallelScopes`,
`memoParentLookup`, `freshDropsMemoization`, `declareIdentity`, `orDieUnwrap`,
`launchHoldsScope`.

---

## 8. `context-tail.ts` — the `Context` surface

New. There is no Effect4 carrier for this family:
`Effect4/Context/Environment.lean` is an 8-line stub, which is why
`layer.build-with-memo-map-service`, `layer.build-uses-ambient-scope` and
`scope.acquire-release`'s "captured context" clause have nothing to be stated
over (deep-state-models §1, findings 8 and 16). This is the rc.112 surface such
a carrier has to meet.

| Row | rc.112 call | source |
| --- | --- | --- |
| `empty` | `Context.empty` | `Context.ts:853` |
| `make(key, value)` | `Context.make` | `:874-877` |
| `add(context, key, value)` | `Context.add` | `:915`, `:990-994`, `:1002` |
| `get(context, key)` | `Context.get` = `getUnsafe` | `:1517`, `:1580`, `:1475-1484` |
| `getOption(context, key)` | `Context.getOption` | `:1636`, `:1705-1709` |
| `merge(self, that)` | `Context.merge` | `:1745`, `:1816-1820` |
| `mergeAll(self, that)` | `Context.mergeAll` | `:1861-1871` |
| `pick(context, key)` | `Context.pick` | `:1904-1913` |
| `omit(context, key)` | `Context.omit` | `:1946-1954` |
| `provide(root, context)` | `Effect.provideContext` | `Effect.ts:11667`; `internal/effect.ts:2180-2199` |
| `updateContext(root, key, value)` | `Effect.updateContext` | `Effect.ts:12004`; `internal/effect.ts:2073-2097` |
| `withContext` | `Effect.contextWith` — **rc.112 has no `Effect.withContext`**, §12.5 | `Effect.ts:11346`; `internal/effect.ts:2152-2158` |
| `referenceDefault` | the tail's own counter over `Context.Reference` | `:2002-2009`, `getDefaultValue` `:1582-1588` |

A `Context` is opaque and reaches the wire as its index (`~effect/Context`,
`Context.ts:587`); a tag carries `~effect/Context/Service` (`:41`) instead, so
tags are not branded as contexts. A key is named by index into the tail's table
— the same untyped-`Val` cast `fork-lowering.md` §(b) records for `entry[1]`.

Three rc.112 facts the rows show, all in §10's output:

* `merge` and `mergeAll` copy the *later* map over the earlier: key 0 in both
  answers 8, not 7.
* `get` on an absent **Service** key throws `serviceNotFoundError` (`:1590`)
  rather than failing typed. That is the same host-lookup failure the census
  records for `layer.build-uses-ambient-scope`, and here it would reach the
  trace as a defect.
* a **Reference** is exempt: `getOption` on an empty context answers
  `{"some":41}` and `get` answers `41`, and `referenceDefault` stays at `1`
  however often it is read — `defaultValue()` runs once and is cached on the
  reference object itself. `withContext` answers `[3]` on an empty fiber
  context for the same reason: a `Reference` is always "present".

Five programs: `buildAndRead`, `mergeIsRightBiased`, `pickAndOmit`,
`provideAndUpdate`, `referenceDefault`.

---

## 9. Typechecking

Both gates over the same 30-file project: the repo's `harness/trace/tsconfig.json`
`files` list plus this lane's seven new modules plus `layer-*.ts` and `job-*.ts`
(which the repo's list does not name today).

### 9.1 `tsc --noEmit`, `typescript@7.0.2`

```
=== tsc --noEmit (typescript 7.0.2) over 30 files ===
tsc exit: 0
```

Compiler options are the repo's own, unaltered: `strict`,
`exactOptionalPropertyTypes`, `noUncheckedIndexedAccess`,
`verbatimModuleSyntax`, `moduleResolution: bundler`,
`allowImportingTsExtensions`, `target ES2022`, `types: ["node"]`.

### 9.2 `@effect/tsgo@0.38.0` diagnostics, `--strict`

```
Effect version per file:
  …/fixture.ts: detected=v4, supported=v4
  …/atoms.ts: detected=v4, supported=v4
  …/tracer.ts: detected=v4, supported=v4
  …/tail.ts: detected=v4, supported=v4
  …/flow-fixture.ts: detected=v4, supported=v4
  …/flow-tail.ts: detected=v4, supported=v4
  …/structured-fixture.ts: detected=v4, supported=v4
  …/structured-tail.ts: detected=v4, supported=v4
  …/scope-fixture.ts: detected=v4, supported=v4
  …/scope-tail.ts: detected=v4, supported=v4
  …/fiber-fixture.ts: detected=v4, supported=v4
  …/fiber-tail.ts: detected=v4, supported=v4
  …/wire-tail.ts: detected=v4, supported=v4
  …/deferred-fixture.ts: detected=v4, supported=v4
  …/deferred-tail.ts: detected=v4, supported=v4
  …/ref-fixture.ts: detected=v4, supported=v4
  …/ref-tail.ts: detected=v4, supported=v4
  …/fibers-fixture.stub.ts: detected=v4, supported=v4
  …/fibers-tail.ts: detected=v4, supported=v4
  …/refs-fixture.stub.ts: detected=v4, supported=v4
  …/deferreds-fixture.stub.ts: detected=v4, supported=v4
  …/scopes-fixture.stub.ts: detected=v4, supported=v4
  …/layers-fixture.stub.ts: detected=v4, supported=v4
  …/context-fixture.stub.ts: detected=v4, supported=v4
  …/context-tail.ts: detected=v4, supported=v4
  …/layer-fixture.ts: detected=v4, supported=v4
  …/layer-tail.ts: detected=v4, supported=v4
  …/job-fixture.ts: detected=v4, supported=v4
  …/job-tail.ts: detected=v4, supported=v4
  …/job-queue.ts: detected=v4, supported=v4
Checked 30 files out of 30 files.
0 errors, 0 warnings and 0 messages.
tsgo exit: 0
```

The severities are the repo's own: `floatingEffect`, `missingEffectError`,
`missingEffectContext` and `schemaSyncInEffect` at `error`, everything else
`off`.

---

## 10. Running the tails

Not part of the acceptance, but done, because a tail that typechecks and cannot
run is not a tail. `node --experimental-strip-types` v22.23.2, against the same
linked installation.

**Sixty programs, zero failures, no tracer defect on any of them.** The three
`Failure` exits are frontiers by construction: the pre-existing
`deferred/deferredPendingAwait`, plus this lane's `layer/launchHoldsScope`
(`Layer.launch` runs `never`) and `fibers/emptyRace` (`Effect.raceAll([])`
resumes nobody, `internal/effect.ts:1493-1495`).

**All 34 pre-existing goldens still match byte for byte.**
`C:\Users\kokok\Dev\effect4-host\l2-goldens.ps1` replays each
`generated/traces/{ref,deferred,scope,layer,fiber}/*.tsv` with its own tape and
diffs the tail's rows against the golden's:

```
=== 34 goldens compared, 0 mismatches ===
```

covering `ref/` (7), `deferred/` (6), `scope/` (4), `layer/` (8) and `fiber/`
(9). That is the receipt for "no existing behaviour changed".

---

## 11. The stubs

Six, all beside their tail, all marked `// STUB: replaced by the generated
fixture` on line 1. Each declares the service class, the `Rows` table, and the
lowered programs the tail runs; the L1 and L3 lanes replace them. There is no
separate root-table stub: `fibers-fixture.stub.ts` carries it, because in the
emitted module the root table *is* part of the lowered flow.

| Stub | Declares | Replaced by |
| --- | --- | --- |
| `harness/trace/fibers-fixture.stub.ts` | `FibersService`, `Fibers`, `FibersRows` (12 rows), `rootEntryBase`, `fibersEntry`, `fibersRoots`, 8 programs | the L1 fixture emitted from `Effect4/Target/TypeScript/FiberProfile.lean` |
| `harness/trace/refs-fixture.stub.ts` | `RefsFullService`, `RefsFull`, `RefsFullRows` (13 rows), 5 programs | the full-surface `Refs` fixture |
| `harness/trace/deferreds-fixture.stub.ts` | `DeferredsFullService`, `DeferredsFull`, `DeferredsFullRows` (15 rows), 5 programs | the full-surface `Deferreds` fixture |
| `harness/trace/scopes-fixture.stub.ts` | `ScopesFullService`, `ScopesFull`, `ScopesFullRows` (12 rows), 4 programs | the full-surface `Scopes` fixture |
| `harness/trace/layers-fixture.stub.ts` | `LayersFullService`, `LayersFull`, `LayersFullRows` (15 rows), 7 programs | the full-surface `Layers` fixture |
| `harness/trace/context-fixture.stub.ts` | `ContextsService`, `Contexts`, `ContextsRows` (13 rows), 5 programs | the `Contexts` fixture |

The `fibers` stub is the one whose replacement is imminent: the L1 lane landed
`Effect4/Target/TypeScript/FiberProfile.lean` and its twelve rows during this
lane, and this stub was aligned to it — same names, same request and answer
spellings, same `rootEntryBase = 1000`, same block-id convention for a root.
What L1 has not yet emitted is a *fixture module* under `harness/trace/`.

---

## 12. What rc.112 has no public API for

Each of these makes the corresponding Lean row a **refusal**, not a claim.

### 12.1 The children set — `childrenSnapshot` and `awaitChildren`

The tracked children live on the fiber *implementation*: the field is
`_children` (`internal/effect.ts:534`), the accessor is `children()`
(`:703-705`), and `forkUnsafe` populates it **only for a non-daemon fork**
(`:5279-5282`), so a `forkDetach` or `forkIn` child is never tracked. The
public `Fiber.Fiber` interface (`Fiber.ts:70-92`) exposes neither the field nor
the accessor, and the package's `exports` map sends `./internal/*` to `null`,
so `FiberImpl` cannot be imported. The only public combinator is the **fused**
`Effect.awaitAllChildren` (`Effect.ts:17207`, `internal/effect.ts:5314-5334`),
which snapshots before and awaits after *one* effect and never hands the
snapshot out.

The tail reads rc.112's own state through a documented cast — it simulates
nothing and computes nothing rc.112 does not hold — but the Lean rows
`childrenSnapshot` and `awaitChildren` must be refusals until rc.112 exports
the pair. `FiberSet` was checked and is not that surface.

### 12.2 A `Layer`'s raw builder

`Layer.build(memoMap, scope)` is a member of the exported interface at
`Layer.ts:56`, carries the doc tag `@internal`, and is **stripped from the
shipped declarations**: `dist/Layer.d.ts:44-48` has no `build`. So `fresh`'s own
one-line spelling at `Layer.ts:3851` cannot be written by a consumer, and any
row that needs to re-wrap an existing layer's builder has to go through
`buildWithMemoMap` instead. That was found by the compiler, not by reading.

### 12.3 `Layer.memoize`

There is no such export at this pin. Memoization is `Layer.fromBuildMemo`
(`:380-388`), which ties the layer to itself through
`memoMap.getOrElseMemoize(self, scope, build)`; `Layer.effect` and
`Layer.effectContext` are the ordinary route to it (`:1439`, `:1481`). Because
of §12.2 the only builder a consumer can hand `fromBuildMemo` is
`buildWithMemoMap`, which is `self.build(memoMap, scope)` **plus** installing
the memo map as the `CurrentMemoMap` service and adding it to the produced
context (`:761-765`). The tail's `memoize` therefore memoizes exactly as rc.112
memoizes, and carries that one extra service; the Lean row must record the
difference rather than claim `fromBuildMemo ∘ build`.

### 12.4 `Scope.extend`

Not an export at this pin. v4's name for "provide the scope to a program
without closing it" is `Scope.provide` (`Scope.ts:310-387` =
`internal/effect.ts:3932-3936`, which is `provideService(scopeTag)`). The
closing form is `Scope.use` (`:616-661` = `:3950-3959`). The tail's `extend`
row is `Scope.provide`, and the row name should be reconsidered at the landing.

### 12.5 `Effect.withContext`

Not an export at this pin. The reader is `Effect.contextWith`
(`Effect.ts:11346` = `internal/effect.ts:2156-2158`,
`withFiber(fiber => f(fiber.context))`), and `Effect.context()` (`:2152`) is
the same read as a value.

### 12.6 Two corrections to `workshop/Deep/fork-lowering.md` §(c)

The host sketch there is wrong against rc.112 in two spellings. Neither affects
the Lean side; both are corrected in `fibers-tail.ts` and are recorded here so
the document can be fixed at the landing.

* **`Effect.forkDaemon` does not exist at this pin.** The daemon fork is
  `Effect.forkDetach` (`Effect.ts:17168` = `internal/effect.ts:5287-5311`,
  `forkUnsafe(…, daemon = true)`). `harness/trace/fiber-tail.ts` already uses
  the right name.
* **`Effect.yieldNow` is a value, not a call.** `Effect.yieldNow`
  (`Effect.ts:2350`) is `yieldNowWith(0)`; the priority-taking form is
  `Effect.yieldNowWith` (`Effect.ts:2374` = `internal/effect.ts:982-994`).
  `Effect.yieldNow({ priority })` would not typecheck.

Also, §(c) note 1's justification stands but its arithmetic is off by nothing
that matters: `forkIn` does fork a daemon (`internal/effect.ts:5366` passes
`true`), so consulting `daemon` only when `region` is `none` is right.

### 12.7 Two losses of the answer alphabet, not of rc.112

Recorded here because they are the same shape as the refusals above and will be
mistaken for them otherwise.

* **A cause with no `Fail` reason has no `Val` preimage.** `awaitFiber` answers
  `Result.fail` carrying an absence, which wires as unit; the profile's
  `exitAsValue` (`ForkFlow.lean:330-338`) takes the same projection and records
  it as a loss.
* **`Deferred.poll` cannot answer for an interrupted cell.** `Effect.result`
  catches a typed failure and not an interrupt, so the only total reading of a
  stored completion into a `Result` is not total over rc.112's completion
  space. §5.

---

## 13. Files

| File | What |
| --- | --- |
| `harness/trace/fibers-tail.ts` | the twelve-row fiber profile over rc.112 |
| `harness/trace/context-tail.ts` | the `Context` surface over rc.112 |
| `harness/trace/{ref,deferred,scope,layer}-tail.ts` | the four store tails, each with its full-surface service beside the pinned narrow one |
| `harness/trace/{fibers,refs,deferreds,scopes,layers,context}-fixture.stub.ts` | the six stubs |
| `C:\Users\kokok\Dev\effect4-host\` | the pinned installation, outside the repository |
| `C:\Users\kokok\Dev\effect4-host\l2-{pin-check.mjs,typecheck.ps1,goldens.ps1}` | the three checks of §1.3, §9 and §10 |
