# The Effect surface as a sugar scout: what our authoring layer should mirror, and what our data language fixes

Read-only survey of the pinned source at `vendor/effect-4.0.0-rc.112/src`, run 2026-09-16 against our side as it
stands at `6ec6485b` plus the working tree (`select` landed in `src/Effect4/Program/Eff.lean:367`, the three
`select` rows in `tools/Effect4Gen/binders.json:27-29`, `src/Effect4/Program/Authoring/Lifts.lean` not yet
regenerated for them). Every claim is cited as file:line in the pinned tree or in ours. Written incrementally;
the receipt in §9 says what was read in full, skimmed, and not reached.

## 1. The answer in ten sentences

The single largest thing to mirror is not a combinator but a type: rc.112's `Filter<Input, Pass, Fail>`
(`Filter.ts:44`) is our `Decision` (`src/Effect4/Program/Decision.lean:36`) with the arms erased into
TypeScript's `ExtractTag`/`ExcludeTag`; the string `Filter.Filter<` appears 84 times outside its own module
(`internal/effect.ts` 26, `Stream.ts` 21, `Effect.ts` 18, `Channel.ts` 12, `Option.ts` 3, `Chunk.ts` 3,
`Sink.ts` 1), and it carries a whole composition algebra
(`or`, `zip`, `zipWith`, `andLeft`, `andRight`, `compose`, `composePassthrough`, `mapFail`, `toOption`,
`toResult`, `toPredicate`, `fromPredicate`) that our `Decision` should acquire as data with `arms`/`decide`
laws rather than as closures. Second: almost everything in `Effect.ts` that looks like a new primitive is a
fold over four things we already have (`bind`, `select`, `catchIf`/`catchCause`, and a loop), so the right
answer to nearly every family below is "sugar", and the census bears it out (`when`, `as`, `asVoid`, `tap`,
`zip`, `zipWith`, `andThen`, `flatten`, `ensuring`, `timeout`, `result`, `option`, `partition`, `reduce`,
`forEach` sequential, `retry`, `repeat`, `catchTag`, `catchTags`, `catchNoSuchElement`, `filterOrFail`,
`orElseSucceed`, `acquireUseRelease` are all definitional in the pinned source). Third: `forEach` with
`concurrency: 1` is literally `whileLoop` with the iterator state in a JS closure
(`internal/effect.ts:4706-4730`), which makes every `forEach`/`all`/`partition`/`reduce`/`validate`/`findFirst`
a fold into our `iterate` once the loop carrier lands, and the concurrent variants a fold into
`withFiber`/`raceAll` plus a semaphore. Fourth: `catchTag`'s residual is real, since
`catchIf(self, isTagged(k), f, orElse)` (`internal/effect.ts:2919-2925`) binds the miss arm at
`ExcludeTag<E, K>`, so our `.tag`
decision's `Ty.diffTag` residual (`src/Effect4/Program/Ty.lean:591`) is not an invention, it is the thing
TypeScript computes structurally and we compute decidably. Fifth: exhaustiveness in Effect is either a
type-level obligation that a runtime `throw` backs up (`Match.exhaustive` throws
`"effect/match/Match/exhaustive: absurd"`, `internal/matcher.ts:647`, `:663`, `:674`) or nothing at all
(`Schema.TaggedUnion`'s `match` calls `handler(value)` where `handler` may be `undefined`,
`Schema.ts:6360-6374`; `catchTags`'s `Cases` keys are all optional, `internal/effect.ts:2929-2936`), whereas
our residual-is-`never` test is a decidable fact of the typing fold and the missing arm is a refusal with a
path. Sixth: `Schedule` is an opaque closure over mutable JavaScript state (`Schedule.fibonacci` keeps `a`,
`b` in a closure, `Schedule.ts:1122-1140`; `metadataFn` keeps `n`, `previous`, `start`,
`Schedule.ts:262-275`), so no consumer can ask a composed policy whether it terminates or what its worst-case
elapsed time is; a schedule as data folded into `iterate` answers both by a fold. Seventh: Effect encodes
loop and stream termination in the *error* channel (`Pull<A, E, Done, R> extends Effect<A, E | Cause.Done<Done>, R>`,
`Pull.ts:39-41`, and `retryOrElse` catches `Cause.isDone` to stop, `internal/schedule.ts:42-46`), which
forces every signature downstream to carry `ExcludeDone`; a loop whose exit is an arm of the construct pays
none of that. Eighth: the nine `*Eager` exports (`mapEager`, `flatMapEager`, `mapErrorEager`, `mapBothEager`,
`catchEager`, `matchEager`, `matchCauseEager`, `matchCauseEffectEager`, `fnUntracedEager`) exist only to
shortcut when the effect is already an `Exit` (`internal/effect.ts:1741-1744`, `:1789`): a peephole rewrite
leaked into the public API, which on our side is one `AlgMap` over `Eff` with a meaning-preservation theorem.
Ninth: the shape worth copying wholesale is the *entry*, name plus input schema plus success schema plus
error schema, because rc.112 spells it four separate times (`Tool.make` `unstable/ai/Tool.ts:1204`,
`Rpc.make` `unstable/rpc/Rpc.ts:902`, `HttpApiEndpoint.make` `unstable/httpapi/HttpApiEndpoint.ts:979`,
`Activity.make` `unstable/workflow/Activity.ts:123`), and it is exactly our `Row`
(`src/Effect4/Program/Eff.lean:190-213`) with a schema on each column. Tenth: the honest count of things that
would need a *new core construct* is three and only one is worth it: a memoized suspension keyed by path
(for `Effect.cached`, `internal/effect.ts:4291`), a first-race-to-exit action (for `timeout`, which uses
`raceFirst` not `raceAll`, `internal/effect.ts:3700-3703`), and an ambient-restoring mask (for
`uninterruptibleMask`'s `restore`, `internal/effect.ts:4340-4352`); everything else in this note is a row, a
form, a `Decision`, or a fold.

## 2. The classified table

Classification vocabulary, as the brief sets it: **row** (a `Row` in a table, `src/Effect4/Program/Eff.lean:190`),
**form** (a `Codegen.Forms.Form` with holes, `src/Effect4/Codegen/Forms.lean:75-87`), **sugar** (a definition in
`Authoring/Sugar.lean` over the generated lifts), **Decision** (a new constructor of
`src/Effect4/Program/Decision.lean:36`), **core** (a new `Eff` constructor), **out of scope**.

### 2.1 `Effect`: construction, sequencing, discarding

| family | pinned citation | class | our side |
| --- | --- | --- | --- |
| `succeed`, `fail`, `failCause`, `sync`, `suspend` | `Effect.ts:1437`, `:2123`, `:2182`, `:1607`, `:1564`; the `suspend` primitive `internal/effect.ts:939-945` | already representable | `Eff.succeed/.fail/.failCause/.sync/.suspend`, `Eff.lean:306-312` |
| `die` | `Effect.ts:2252` | already a form | `Forms.all` `"die"`, `Forms.lean:91` |
| `void` (the value) | `Effect.ts:3936` `asVoid` | already a form | `Forms.all` `"void"`, `"asVoid"`, `Forms.lean:90`, `:101` |
| `flatMap` | `internal/effect.ts:1590` | already representable | `Eff.bind` (`Eff.lean:315`); sugar `flatMap`, `Sugar.lean:30` |
| `map` | `internal/effect.ts:1759` | sugar (fold) | `bind` then `succeed (app atom v)`; `Sugar.lean:36` |
| `andThen` (effect / continuation / thunk) | `internal/effect.ts:1417-1439` | already a form, three rows | `Forms.all` `"andThenEffect"`, `"andThenContinuation"`, `"andThenThunk"`, `Forms.lean:93-98` |
| `as` | `internal/effect.ts:1386-1400` | already a form | `Forms.all` `"as"`, `Forms.lean:99` |
| `tap` (continuation / effect) | `internal/effect.ts:1442-1464` | already a form | `Forms.all` `"tapContinuation"`, `"tapEffect"`, `Forms.lean:103-106` |
| `zip`, `zipWith` (sequential) | `internal/effect.ts:2284-2307` | sugar (fold) | `bind a (bind b (succeed (app "pair" [v0, v1])))`; missing today |
| `zip`, `zipWith` (`{concurrent:true}`) | `internal/effect.ts:2304-2306` | sugar over `all` | `all([a,b],{concurrency:2})`, so a fork-join fold (see §7) |
| `zipLeft`, `zipRight` | not exported in rc.112 (`zipRight`/`zipLeft` live on `Option.ts:2308`, `:2397`) | n/a for `Effect` | rc.112 dropped them; `andThen` covers |
| `flatten` | `internal/effect.ts:1754-1756` | out of scope as a value, sugar where the inner program is static | see §8 addendum B |
| `Do`, `bindTo`, `bind` (do-notation) | `internal/effect.ts:5175-5191` | already representable | our positional environment (decision D1, `Eff.lean:19-22`) *is* the accumulated record; `bind` with a name is `bindTo` |
| `gen` | `internal/effect.ts:1175-1196` | already representable (reader-only) | `Eff.gen (body : Stmts Op)`, `Eff.lean:316`; `binders.json` profile `readerOnly` |
| `fn`, `fnUntraced` | `Effect.ts:17824`, `internal/effect.ts:1199` | out of scope for the core; an authoring-layer definition | a Lean function returning `Src Op` is already this |
| `promise`, `tryPromise` | `internal/effect.ts:1051-1060` | row (async, external) | `NativeOp.external` + `registration := .external`, `Native.lean:130`, `:359` |
| `mapEager`/`flatMapEager`/`matchEager`/… (9) | `internal/effect.ts:1728-1790`, `:3559`, `Effect.ts:25016-25649` | out of scope (peephole) | one `AlgMap` rewrite over `Eff` with a `meaning` preservation theorem |

### 2.2 `Effect`: control by value

| family | pinned citation | class | our side |
| --- | --- | --- | --- |
| `when` | `internal/effect.ts:2360-2376` | sugar (fold) | `bind cond (select (var 0) .bool (map some self) (succeed none))` |
| `if` / `unless` | absent in rc.112 (`grep` finds neither in `Effect.ts` nor `internal/effect.ts`) | n/a | our `ifElse` is already `branch`/`select .bool`, `Sugar.lean:40`; `Eff.branch`, `Eff.lean:326` |
| `match`, `matchEffect` | `internal/effect.ts:3559`, `Effect.ts:11055` | already representable | `Eff.matchCause` with a `select` on the cause, or the form `"matchCauseEffect"`, `Forms.lean:111` |
| `filterOrFail`, `filterMapOrFail`, `filterOrElse`, `filterMapOrElse` | `internal/effect.ts:2315` onward, `Effect.ts:9439`-`9991` | sugar over a `Decision` | `select s d (fail …) (succeed …)`; the `Decision` is the filter |
| `filter`, `filterMap`, `filterMapEffect` (on iterables) | `Effect.ts:9073`, `:9276`, `internal/effect.ts:5105` | sugar over `iterate` + `Decision` | list fold with a decision at each step |
| `findFirst`, `findFirstFilter` | `Effect.ts:910`, `:978`, `internal/effect.ts:4600-4616` | sugar over `iterate` + `Decision` | the pinned implementation is a recursive `flatMap` loop |
| `head` | `Effect.ts:1254` | sugar over a `listCase` decision | see §4 |
| `option`, `result`, `exit` | `internal/effect.ts:3412`, `:3417`, `:3621` | see §8 addendum B | `Eff.exit` exists (`Eff.lean:321`); `option`/`result` are folds over it |
| `transposeOption`, `fromOption`, `fromResult`, `fromNullishOr` | `Effect.ts:2509`, `:2462`, `:2423`, `:2538` | sugar over an option/result `Decision` | |

### 2.3 `Effect`: failure

| family | pinned citation | class | our side |
| --- | --- | --- | --- |
| `catchCause` | `Effect.ts:5312`; our `arms` row cites `internal/effect.ts:2417` | already representable | `Eff.catchCause`, `Eff.lean:318` |
| `catch_` (`Effect.catch`) | `internal/effect.ts:2558-2572` | already representable | `catchCause` + `findError`; `catchIf` with a constant-true test |
| `catchIf` (predicate + handler + **orElse**) | `internal/effect.ts:2760-2811` | **gap**: our `catchIf` has no `orElse` arm | `Eff.catchIf` is test/body/handler, `Eff.lean:356-360`; see §5 |
| `catchFilter` | `internal/effect.ts:2814-2846` | needs a `Decision` on the error | `catchIf` generalised the way `select` generalised `branch` |
| `catchTag` (one tag or a list) | `internal/effect.ts:2919-2925` = `catchIf(self, isTagged(k), f, orElse)` | sugar over `catchFilter` with `.tag` | |
| `catchTags` (handler table + orElse) | `internal/effect.ts:2990-3005` = `catchFilter` over `Object.keys(cases)` | sugar: `foldr` over `catchTag` | our `matchTag`'s error-channel twin |
| `catchReason`, `catchReasons` | `internal/effect.ts:3007`, `:3111`; `Filter.reason` `Filter.ts:643-682` | needs a nested-tag `Decision` | `.tag` composed with `.tag` under a field |
| `catchCauseFilter` | `internal/effect.ts:2532-2554` | needs a `Decision` on `Cause` | our `CauseTerm` is data, so the decision is decidable |
| `catchDefect`, `catchNoSuchElement` | `internal/effect.ts:2587`, `:2575` | sugar | `matchCause` + a cause decision |
| `mapError`, `mapBoth` | `Effect.ts:6172`, `:6296` | sugar (fold) | `catchCause (fail (app atom (var 0)))`; a form |
| `orDie` | `Effect.ts:6419` | already in the unary-ref table | `Forms.unaryRefs` `"Effect.orDie"`, `Forms.lean:166` |
| `orElseSucceed`, `firstSuccessOf` | `Effect.ts:8124`, `:8248` | sugar | `catchCause (succeed v)`; `foldr` over `catchCause` |
| `sandbox` | `internal/effect.ts:1472-1474` = `catchCause(self, fail)` | sugar | needs a cause-as-value type; see §6 |
| `ignore`, `ignoreCause` | `internal/effect.ts:3333`, `:3376` | sugar | `matchCause (succeed unit) (succeed unit)` |
| `tapError`, `tapErrorTag`, `tapCause`, `tapCauseIf`, `tapCauseFilter`, `tapDefect` | `Effect.ts:6453`-`6980` | sugar over `catchCause` + a `Decision` | |
| `eventually` | `Effect.ts:7086` | sugar over `iterate` | retry forever |
| `retry`, `retryOrElse` | `internal/schedule.ts:131`, `:51` | sugar over `iterate` + a schedule fold | see §5 |
| `repeat`, `repeatOrElse`, `schedule`, `scheduleFrom`, `forever`, `replicate` | `internal/schedule.ts:13`, `:200`; `Effect.ts:14480`, `:15258` | sugar over `iterate` | |
| `withExecutionPlan` | `Effect.ts:7897`; `ExecutionPlan.ts:169` | sugar over `foldr` of `catchIf` + `retry` | a plan is a list of `{provide, attempts, schedule, while}` |

### 2.4 `Effect`: resources, interruption, scope

| family | pinned citation | class | our side |
| --- | --- | --- | --- |
| `scope`, `scoped`, `scopedWith` | `Effect.ts:12775`-`12859` | already representable | `Eff.scoped`, `Eff.lean:340` (lift renamed `scope`, `binders.json:52`) |
| `acquireRelease` (scope-registering) | `internal/effect.ts:3971-3987` | already representable / form | `Eff.acquireRelease`, `Eff.lean:342`; form `"releaseOne"`, `Forms.lean:122` |
| `acquireUseRelease` | `internal/effect.ts:4201-4213` | **form with a hole, blocked**: `Template` has no `uninterruptible`/`interruptible` node (`Forms.lean:31-43`) | add two `Template` constructors; see §5 |
| `addFinalizer` | `internal/effect.ts:3990-3999` | row over the scope store | `Scope.addFinalizer` is not in `NativeOp` today (`Native.lean:101-130`) |
| `ensuring` | `internal/effect.ts:4043-4057` = `onExit(self, _ => finalizer)` | already a form | `Forms.all` `"ensuring"`, `Forms.lean:107` |
| `onExit`, `onExitIf`, `onExitFilter`, `onError`, `onErrorIf`, `onErrorFilter` | `internal/effect.ts:4032`, `:4060`, `Effect.ts:13262`-`13707` | `onExit` representable; the `If`/`Filter` variants need an exit `Decision` | `Eff.onExit`, `Eff.lean:320` |
| `onInterrupt` | `internal/effect.ts:4184-4198` | sugar over `onExit` + a cause decision | |
| `uninterruptible`, `interruptible` | `internal/effect.ts:4302`, `Effect.ts:14199` | already representable | `Eff.uninterruptible`, `.interruptible`, `Eff.lean:323-324` |
| `uninterruptibleMask`, `interruptibleMask` | `internal/effect.ts:4340-4367` | **needs a third mask mode (restore-to-ambient)** | `MaskMode.inherit` already exists for forks (`src/Effect4/Machine/Supervision.lean:15`) but not as a region; see §6 |
| `interrupt`, `Fiber.interrupt*` | `internal/effect.ts:4299`; `Fiber.ts:354`-`574` | already representable | `ActionTerm.interrupt`, `.interruptAll`, `Eff.lean:393`, `:395` |
| `abortSignal` | `internal/effect.ts:4370-4376` | row (host-only) | an external row |
| `cached`, `cachedWithTTL`, `cachedInvalidateWithTTL` | `internal/effect.ts:4291`; `Effect.ts:13869`, `:14036` | **new core construct or a memo row**; see §6 | |

### 2.5 `Effect`: concurrency

| family | pinned citation | class | our side |
| --- | --- | --- | --- |
| `forEach` (`concurrency: 1`) | `internal/effect.ts:4706-4730`, literally `whileLoop` | sugar over `iterate` | |
| `forEach` (`concurrency > 1`) | `internal/effect.ts:4683-4704`, `forEachConcurrent` `:4939` | sugar over fork + semaphore + join | |
| `all` (iterable / struct / record, `discard`, `mode:"result"`) | `internal/effect.ts:4383-4421`, where all four cases delegate to `forEach` | sugar | |
| `partition`, `reduce`, `validate`, `findFirst` | `internal/effect.ts:4424-4445`, `:4448`, `Effect.ts:748`, `:910` | sugar over `forEach`/`iterate` | |
| `race`, `raceAll` (first **success**) | `internal/effect.ts:1477-1533`, `:1583` | already representable | `ActionTerm.raceAll`, `Eff.lean:400`; witness `src/Effect4/Laws/Machine/Witnesses.lean:386` |
| `raceFirst`, `raceAllFirst` (first **exit**) | `internal/effect.ts:1535-1581`, `:1623` | **gap**: not modelled; `timeout` needs it | see §6 |
| `timeout`, `timeoutOption`, `timeoutOrElse` | `internal/effect.ts:3677-3727` = `raceFirst(self, flatMap(sleep(d), orElse))` | form once `raceFirst` exists | `NativeOp.sleep` already exists, `Native.lean:125` |
| `forkChild`, `forkDetach`, `forkIn`, `forkScoped` | `Effect.ts:16990`-`17168` | already forms | `Forms.all` `"forkChildDefault"`… `Forms.lean:114-121` |
| `awaitAllChildren`, `Fiber.awaitAll`, `Fiber.join*` | `Effect.ts:17207`; `Fiber.ts:235`, `:279` | already representable | `ActionTerm.awaitAll`, `Eff.awaitFiber`, `Eff.lean:396`, `:337` |
| `yieldNow`, `yieldNowWith` | `Effect.ts:2350`, `:2374` | already representable | `Eff.yieldNow`, `Eff.lean:333` |
| `Semaphore`, `Latch`, `PartitionedSemaphore` | `Semaphore.ts:358`, `Latch.ts:196`, `PartitionedSemaphore.ts:322` | rows over new stores | see §7 |
| `FiberHandle`, `FiberMap`, `FiberSet` | `FiberHandle.ts:146`, `FiberMap.ts:162`, `FiberSet.ts:154` | sugar over a scope plus a handle store | see §7 |
| `Pool`, `RcMap`, `RcRef` | `Pool.ts:232`, `RcMap.ts:240`, `RcRef.ts:157` | rows over new stores | |

### 2.6 Services, context, layers, config

| family | pinned citation | class | our side |
| --- | --- | --- | --- |
| `Context.Key`, `Service`, `Reference` | `Context.ts:64`, `:201`, `:485` | already representable | `ServiceKey` (`src/Effect4/Machine/Key.lean`), `nativeServiceTy` `Native.lean:302` |
| `service`, `serviceOption`, `provideService`, `provideServiceEffect`, `updateService` | `Effect.ts:11914`-`12623` | `service`/`provideService` representable; the rest sugar | `Eff.service`, `.provideService`, `Eff.lean:352`, `:355` |
| `provide`, `provideContext`, `setContext`, `updateContext`, `contextWith` | `Effect.ts:11383`-`12004` | already representable | `Eff.provideLayer`, `ActionTerm.setContext`/`.getContext`, `Eff.lean:349`, `:401-402` |
| `Layer.*` (`effect`, `effectDiscard`, `provide`, `provideMerge`, `merge`, `mergeAll`, `fresh`, `orDie`) | `Layer.ts:1427`, `:1512`, `:2258`, `:2704`, `:1850`, `:1652`, `:3850`, `:3327` | already representable | `LayerTerm`, `Eff.lean:414-446`, a one-for-one transcription |
| `Layer.*` beyond those (`LayerMap`, `LayerRef`, `ManagedRuntime`) | `LayerMap.ts`, `LayerRef.ts`, `ManagedRuntime.ts` | not reached | |
| `Config.*` (`string`, `map`, `mapOrFail`, `orElse`, `withDefault`, `option`, `nested`, `Record`) | `Config.ts:252`-`1943`; `Config<T> extends Effect<T, ConfigError>` `Config.ts:108-112` | **form family or a small data type**; a `Config` is already a description with a `parse(provider)` step | see §7 |
| `ConfigProvider` | `ConfigProvider.ts` | row (external) | |

### 2.7 Data modules (elimination shapes)

| family | pinned citation | class | our side |
| --- | --- | --- | --- |
| `Option.match`, `isNone`, `isSome`, `getOrElse`, `filter`, `filterMap` | `Option.ts:403`, `:344`, `:371`, `:647`, `:3304`, `:3200` | `Decision .option` (landed) | `Decision.option`, `Decision.lean:36-48` |
| `Option.gen`, `Option.Do`, `Option.bind`, `Option.bindTo` | `Option.ts:4305`, `:4268`, `:4171`, `:4027` | out of scope (a second monad in the value language) | a `Ty.option` value plus `select .option` covers the uses |
| `Result.match`, `isFailure`, `isSuccess`, `merge`, `flip` | `Result.ts:1182`, `:689`, `:721`, `:1689`, `:2748` | **needs a `Decision .result`** | see §4 |
| `Exit.match`, `isSuccess`, `isFailure`, `filterSuccess`, `filterValue`, `filterFailure`, `filterCause`, `findError`, `findDefect` | `Exit.ts:752`, `:393`, `:421`, `:545`, `:582`, `:616`, `:651`, `:686`, `:721` | **needs a `Decision .exit`** (and every `filter*` is a `Filter`) | see §4 |
| `Cause` (`fail`, `die`, `interrupt`, `fromReasons`, `combine`, `findFail`, `findError`, `findDie`, `findInterrupt`, `hasInterruptsOnly`, `interruptors`, `annotate`) | `Cause.ts:482`-`1948` | `CauseTerm` covers the constructors; the `find*`/`has*` are `Decision`s on a cause | `CauseTerm`, `Eff.lean:271-277` |
| `Cause`'s built-in tagged errors (`NoSuchElementError`, `Done`, `TimeoutError`, `IllegalArgumentError`, `ExceededCapacityError`, `AsyncFiberError`, `UnknownError`) | `Cause.ts:1319`, `:1408`, `:1513`, `:1570`, `:1632`, `:1716`, `:1785` | rows / literal error types | our error language is `rawSupportedErrTy`, `Eff.lean:55-60` |
| `Match.*` (`type`, `value`, `when`, `whenOr`, `whenAnd`, `tag`, `tags`, `tagsExhaustive`, `discriminator*`, `not`, `orElse`, `orElseAbsurd`, `exhaustive`, `option`, `result`) | `Match.ts:314`-`2193` | sugar over nested `select` with `Decision`s | our `matchTag` fold; see §3 and §5 |
| `Filter.*` (the whole module) | `Filter.ts:126`-`1185` | **`Decision` constructors plus a `Decision` algebra** | see §4 |
| `Predicate`, `Order`, `Equivalence`, `Equal`, `Hash` | `Predicate.ts`, `Order.ts`, … | out of scope for the program AST; atoms of the term language | `NativeAtom`, `src/Effect4/Program/NativeAtom.lean` |

### 2.8 Streaming and messaging

| family | pinned citation | class | our side |
| --- | --- | --- | --- |
| `Queue` (`bounded`, `sliding`, `dropping`, `unbounded`, `offer`, `take`, `takeAll`, `takeN`, `end`, `fail`, `shutdown`) | `Queue.ts:500`-`1858` | rows over one new store | see §7 |
| `PubSub` (`bounded`, `dropping`, `sliding`, `unbounded`, `publish`, `subscribe`) | `PubSub.ts:334`-`1304` | rows over the queue store plus a subscriber list | see §7 |
| `Pull` | `Pull.ts:39-41` | out of scope as a type; its `Done`-in-error trick is a gap (see §5) | |
| `Channel` | `Channel.ts:140-152` | out of scope for now; it is `Effect` producing a `Pull` | |
| `Stream` | `Stream.ts:122-127`, holding `{ channel: Channel<NonEmptyReadonlyArray<A>, E, void, …> }` | out of scope for now; sugar once `Queue` rows and `iterate` exist | see §7 |
| `Sink`, `Take` | `Sink.ts`, `Take.ts` | not reached | |
| `Request`, `RequestResolver` (`batchN`, `grouped`, `setDelay`, `withCache`, `persisted`) | `Request.ts:293`, `RequestResolver.ts:236`-`2017` | sugar over a queue row, a deferred per request, and `iterate` | see §7 |

### 2.9 Schema

| family | pinned citation | class | our side |
| --- | --- | --- | --- |
| `Literal`, `String`, `Number`, `Boolean`, `Struct`, `Tuple`, `Record`, `Union`, `NullOr`, `suspend` | `Schema.ts:2785`, `:3146`, `:3170`, `:3192`, `:3581`, `:4412`, `:3961`, `:4923`, `:5012`, `:5112` | already representable | `Schema/Representation.lean`; combinators missing at the front (workshop §5b item 1) |
| `tag`, `tagDefaultOmit`, `TaggedStruct` | `Schema.ts:6100`, `:6135`, `:6196` | already representable | `Ty.taggedColumn`, `Ty.payloadTy`, `Ty.lean:599`, `:613` |
| `TaggedUnion`, `toTaggedUnion` (with `cases`, `discriminants`, `guards`, `match`, `matchOrElse`) | `Schema.ts:6470`, `:6318-6391` | **mirror as `Decision.ofSchema`**; see §4 | |
| `Class`, `TaggedClass`, `Error`, `TaggedError` | `Schema.ts:14660`, `:14924`, `:15074`, `:15207` | representable as a tagged struct plus an opaque host constructor | the host checker is the oracle for the class identity |
| transformations (`decodeTo`, `encodeTo`, `middlewareDecoding/Encoding`, `catchDecoding/Encoding`, `withConstructorDefault`, `withDecodingDefault*`) | `Schema.ts:5585`-`6058` | out of scope for `Ty`; they belong to the schema document | |
| annotations (`annotate`, `annotateEncoded`, `annotateKey`, `resolveAnnotations`) | `Schema.ts:653`, `:686`, `:721`, `:16931` | already representable | annotations as CAS traits (memory: program-as-schema) |
| `toRepresentation`, `toJsonSchemaDocument`, `toCodecJson`, `toIso`, `toDifferJsonPatch`, `toArbitrary`, `toEquivalence`, `toFormatter` | `Schema.ts:15623`, `:15752`, `:15819`, `:16593`, `:16705`, `:15379`, `:15596`, `:15419` | folds over the schema document, the same catamorphism shape as ours | `Schema/Bridge.lean:114`, `:162` |
| `check`, `refine`, `brand`, `makeFilter`, `makeFilterGroup`, the ~90 `is*` checks | `Schema.ts:5135`, `:5184`, `:5242`, `:6659`, `:6725`, `:6763`-`9587` | out of scope for `Ty`; predicates on the schema document | |

### 2.10 Platform and unstable (what a CLI, an MCP server or an HTTP API touches)

| family | pinned citation | class | our side |
| --- | --- | --- | --- |
| `FileSystem` (a service with ~40 methods), `Path`, `Terminal`, `Stdio` | `FileSystem.ts:663`, `Path.ts:255`, `Terminal.ts:166`, `Stdio.ts:100` | **package tables** exactly as `SqliteBun` | `src/Effect4/Program/Packages.lean:33-38` is the pattern |
| `PlatformError` (`BadArgument`, `SystemError`) | `PlatformError.ts:36`, `:109` | tagged error rows | `rawSupportedErrTy`'s tagged pair, `Eff.lean:57` |
| `ChildProcess` (`StandardCommand`/`PipedCommand` are **data**, with `pipeTo`, `setCwd`, `setEnv`) | `unstable/process/ChildProcess.ts:42`, `:62`, `:816`, `:1066`, `:1147` | a small data type plus one run row | the closest thing in rc.112 to our own design |
| `HttpApi`, `HttpApiGroup`, `HttpApiEndpoint` (payload/success/error schemas), `HttpApiBuilder`, `HttpApiClient` | `unstable/httpapi/HttpApi.ts:228`, `HttpApiEndpoint.ts:979`, `:268-283` | **entries** (§2.11) | |
| `HttpRouter`, `HttpServerRequest`/`Response`, `HttpMiddleware`, `HttpClient` | `unstable/http/HttpRouter.ts:119`, `:504`, `:970` | rows plus a route table as data | |
| `unstable/cli` `Command`, `Flag`, `Argument`, `Prompt`, `HelpDoc`, `Completions` | `unstable/cli/Command.ts:620`, `Flag.ts:35`, `Argument.ts:41`, `Prompt.ts:52` | **data descriptions already**: a `Flag` is a parser description with `map`, `filterMap`, `withDefault`, `withFallbackConfig` | mirror as a schema-carrying entry |
| `unstable/ai` `Tool`, `Toolkit`, `McpServer`, `LanguageModel`, `Prompt`, `Response` | `unstable/ai/Tool.ts:1204`, `Toolkit.ts:496`, `McpServer.ts:1515`, `:1673`, `:1981` | **entries** | the inspection protocol's tool table |
| `unstable/rpc` `Rpc`, `RpcGroup`, `RpcServer`, `RpcClient` | `unstable/rpc/Rpc.ts:902`, `RpcGroup.ts:402` | **entries** | |
| `unstable/sql` `SqlClient`, `Statement`, `SqlSchema`, `SqlResolver`, `Migrator` | `unstable/sql/SqlClient.ts` | already a package on our side | `Packages/SqliteBun.lean` |
| `unstable/persistence` `KeyValueStore`, `Persistence`, `PersistedCache`, `PersistedQueue`, `RateLimiter` | `unstable/persistence/RateLimiter.ts:86`, `:226` | package tables | `Packages/KeyValueStoreMemory.lean` |
| `unstable/workflow` `Workflow`, `Activity`, `DurableDeferred`, `DurableClock`, `WorkflowEngine` | `unstable/workflow/Activity.ts:123`, `Workflow.ts:429`, `:831` | **entries plus the tape**; see §7 | |
| `unstable/cluster`, `unstable/eventlog`, `unstable/devtools`, `unstable/observability`, `unstable/reactivity`, `unstable/workers`, `unstable/socket`, `unstable/encoding`, `unstable/schema` | listed but only skimmed | see receipt | |

### 2.11 The one shape rc.112 repeats four times

`{ name, payload/parameters schema, success schema, error schema, handler }`:
`Tool.make` (`unstable/ai/Tool.ts:1204`), `Rpc.make` (`unstable/rpc/Rpc.ts:902`), `HttpApiEndpoint.make`
(`unstable/httpapi/HttpApiEndpoint.ts:979`, with `getPayloadSchemas`/`getSuccessSchemas`/`getErrorSchemas` at
`:268-283`), `Activity.make` (`unstable/workflow/Activity.ts:123-179`, which additionally derives
`exitSchema = Schema.Exit(successJson, errorJson, Defect())`). That is our `Row`
(`src/Effect4/Program/Eff.lean:190-213`: `name`, `spelling`, `shape`, `trailing`, `kind`, `request`, `answer`,
`error`, `requires`, `cite`, `typeArgs`, `registration`)
with `Ty` replaced by a schema document at each column. The workshop's §5 entry (`module, name, typeParams,
input : Schema, output : Schema, cite`) is the generalisation, and the four sites above are the evidence that
one entry type is enough.

## 3. The ordered sugar list

Each line is a definition in `src/Effect4/Program/Authoring/Sugar.lean` over the generated lifts, with the fold
it is and the `eff` notation line it would carry (abstraction 4 of the select packet §3c).

1. **`ifElse test a b`** is `select test .bool a b`. Already present as `Sugar.ifElse` over `branch`
   (`Sugar.lean:40`); re-point at `selectBool` when the lift is regenerated.
   `eff`: `if test then a else b`.
2. **`optionCase s (onNone := a) (onSome := fun x => b)`** is `select s .option a b`; the fold is the lift
   `selectOption` (`binders.json:28`). Mirrors `Option.match` (`Option.ts:403`) and `Effect.transposeOption`.
   `eff`: `match s with | none => a | some x => b`.
3. **`caseTag s "A" (hit := fun p => a) (miss := fun r => b)`** is `select s (.tag "A") a b`; lift `selectTag`
   (`binders.json:29`). Mirrors `Filter.tagged` (`Filter.ts:552`) and `Predicate.isTagged`.
   `eff`: `match s with | tag "A" p => a | rest => b`.
4. **`matchTag s [("A", …), ("B", …)] (fallthrough := fun rest => …)`** is a `foldr` over `caseTag`, each miss
   typed at the residual so far (`Ty.diffTag`, `Ty.lean:591`); a `never` residual makes the fallthrough
   refusable. Mirrors `Match.tags`/`Match.tagsExhaustive` (`Match.ts:1246`, `:1301`) and
   `Schema.TaggedUnion.match` (`Schema.ts:6360`).
   `eff`: `match s with | tag "A" p => … | tag "B" q => … | rest => …`.
5. **`whenSome s body`, `whenTrue test body`**: `when` (`internal/effect.ts:2360-2376`) is
   `bind cond (select (var 0) .bool (map some body) (succeed none))`. One definition, two spellings.
   `eff`: `when test do body`.
6. **`mapWith atom e`** and **`zipWith atom a b`** are `bind`-then-`succeed` folds. `map` exists
   (`Sugar.lean:36`); `zipWith` is `bind a (bind b (succeed (app atom [var 1, var 0])))`, which is the pinned
   sequential `zipWith` verbatim (`internal/effect.ts:2307`).
   `eff`: `let x ← a; let y ← b; pure (atom x y)`.
7. **`tapWith e (fun v => k)`** is already `Forms."tapContinuation"` (`Forms.lean:103`); give it an authoring
   spelling so `eff` can print it.
   `eff`: `tap e with v => k`.
8. **`forEachList xs (fun x => body)`** is the fold into `iterate` with the cursor `(index, acc)`; the pinned
   `forEachSequential` is exactly this shape with the cursor in a JS closure
   (`internal/effect.ts:4706-4730`). `all`, `partition`, `reduce`, `validate`, `findFirst` are then
   definitions over it (`internal/effect.ts:4383-4445`).
   `eff`: `for x in xs do body`.
9. **`retry policy body`** and **`repeat policy body`** are folds over `iterate` whose cursor is the schedule
   state, the failure caught by `catchIf` and fed back as the next cursor. The pinned `retryOrElse` is
   `forever` + `catch_` on `Cause.isDone` (`internal/schedule.ts:29-46`, `:51`), so ours replaces a sentinel
   error with the loop's own exit arm.
   `eff`: `retry (exponential 100 ×2 upTo 5) do body`.
10. **`timeoutOrElse d body orElse`** is `raceFirst(body, bind (sleep d) orElse)`
    (`internal/effect.ts:3700-3703`), blocked on a first-to-exit race (§6).
    `eff`: `timeout 5000 do body else orElse`.
11. **`acquireUseRelease acquire use release`** is `uninterruptible (bind acquire (onExit (interruptible use) release))`
    (`internal/effect.ts:4201-4213`), blocked on two `Template` constructors (§5).
    `eff`: `use r ← acquire finally release r exit do body`.
12. **`catchTag body "A" (fun p => handler)`** and **`catchTags body [… ] (orElse := …)`** are the error-channel
    twins of 3 and 4, once `catchIf` grows an `orElse` arm or `catchFilter` lands (§5).
    `eff`: `try body catch | tag "A" e => … | rest => …`.
13. **`ensureVoid e` and `ignore e`** are `matchCause e (succeed unit) (succeed unit)`; they mirror
    `internal/effect.ts:3333`.
    `eff`: `ignore e`.
14. **`bindDiscard`** is already `Sugar.andThen` with the `"_"` name (`Sugar.lean:33`); the `eff` statement form
    is a bare `e` line with no `let`.
    `eff`: `e` on its own line.

## 4. The `Decision` constructors worth adding

`Decision` today is `bool | option | tag` (`src/Effect4/Program/Decision.lean:36-48`). Each line below is
`decide` and `arms` in one sentence. The cost of each is one constructor, one `decide` arm, one `arms` arm, one
`binds` arm and one case in `decide_typed`; the packet's §3b ledger says everything else is generated.

| constructor | decides on | arm 0 binds | arm 1 binds | mirrors |
| --- | --- | --- | --- | --- |
| `.result` | a `Result`-shaped value | the failure value at the error column | the success value at the success column | `Result.match` `Result.ts:1182`; `Effect.result` `internal/effect.ts:3417` |
| `.exit` | an `Exit`-shaped value | the cause at `causeOf E` | the success at `A` | `Exit.match` `Exit.ts:752`; `Exit.filterSuccess/.filterFailure` `:545`, `:616` |
| `.list` | a list value | nothing (the empty case) | head and tail, two slots | `Effect.head` `Effect.ts:1254`; every `forEach` step |
| `.lit v` | equality with a literal | nothing (the hit) | the whole value at the residual `Ty.diffLit` | `Filter.equals`/`equalsStrict` `Filter.ts:704`, `:376`; `Match.is` `Match.ts:1447` |
| `.tyIs t` | a type test on a union member | the value at `t` | the value at the residual `t' \ t` | `Filter.string/.number/.boolean` `Filter.ts:353`, `:444`, `:465`; `Match.string` `Match.ts:1479` |
| `.field k d` | the field `k` of a struct, then `d` | what `d`'s arm 0 binds | the whole value at the residual | `Filter.reason` `Filter.ts:643`, `:672-682` (a tag inside a `reason` field) |
| `.cause c` | which reason a cause carries (`fail`/`die`/`interrupt`) | the carried value | the whole cause | `Cause.findFail/.findDie/.findInterrupt` `Cause.ts:910`, `:1013`, `:1085` |

And the two *combinators* on `Decision`, taken from `Filter`'s own algebra, each a constructor whose `decide`
and `arms` are defined from its children (so no new proof obligation beyond one `decide_typed` case each):

| combinator | pinned | meaning |
| --- | --- | --- |
| `.or d e` | `Filter.or` `Filter.ts:714` | hit if either hits; arm 0 binds the joined pass type, arm 1 the intersected residual |
| `.compose d e` | `Filter.compose` `Filter.ts:1043-1096` | run `d`, feed its pass value to `e`; arm 1 binds `d`'s fail joined with `e`'s fail |
| `.not d` | `Match.not` `Match.ts:1350` | swap the arms; `arms` swaps the pair |

The point that makes this cheap on our side and impossible on theirs: `Filter` is a JavaScript function, so
`Filter.compose`'s *type* is hand-written as `Filter<InputL, PassR, FailL | FailR>` (`Filter.ts:1085`) and
nothing checks that the function agrees with it. `Decision.arms` is a total function on `Ty` and
`Decision.decide_typed` (`src/Effect4/Laws/Program/Decision.lean`) is the proof that it does.

`Decision.ofSchema` (workshop §5b item 2) is the last piece. rc.112 already derives a matcher from a schema:
`toTaggedUnion` walks the union's members, collects `SchemaAST.collectSentinels`, and throws
`"Duplicate discriminant"` or `"No literal or unique symbol found"` when the walk fails (`Schema.ts:6325-6359`).
Ours is the same walk, total, returning `Option Decision`, with the duplicate-discriminant case a refusal with
a path instead of a thrown `Error`.

## 5. The gaps we can address more cleanly

**G1. Tagged tuples versus `_tag` objects, and what the residual buys.** rc.112 discriminates on a `_tag`
*property* of an object: `Predicate.isTagged(input, tag)` behind `Filter.tagged` (`Filter.ts:552-600`),
`hasProperty(e, "_tag") && keys.includes(e._tag)` in `catchTags` (`internal/effect.ts:2992-2996`),
`SchemaAST.collectSentinels` finding a literal at the `_tag` key in `toTaggedUnion` (`Schema.ts:6340-6353`).
The residual is then TypeScript's `ExcludeTag<E, K>`, a structural set difference over the union, computed by
the compiler and unavailable to any runtime consumer. We spell the same thing as a two-cell list value
`[tag, payload]` read by `Val.tagPayload?` (`src/Effect4/Program/Decision.lean:31`) over a `taggedColumn` type
whose members are literal-tagged pairs (`src/Effect4/Program/Ty.lean:599`), with the residual `Ty.diffTag` a
member filter (`:591`) and the payload `Ty.payloadTy` a join of the matching members (`:613`). Three things
follow that the `_tag` object cannot give: the residual is a *value of `Ty`* so a later arm can be typed at it
and a tool can print it; `taggedColumn` states exactly when the narrowing is sound, so the agreement with the
host's `Extract`/`Exclude` is a checkable boundary rather than an assumption; and `decide_typed`
(`src/Effect4/Laws/Program/Decision.lean`) proves the runtime reader and the type-level residual are the same
function, which in rc.112 is two independent pieces of code (a JS predicate and a mapped type) that nothing
ties together.

**G2. Exhaustiveness in `catchTag`, `catchTags`, `Match` and `Schema.TaggedUnion`.** Three different
non-answers in one library. `Match.exhaustive` is a type obligation (`Matcher<I, F, never, …>`) backed at
runtime by `throw new Error("effect/match/Match/exhaustive: absurd")` (`internal/matcher.ts:647`, `:663`, `:674`)
, so an exhaustiveness bug becomes a defect at the point of failure, not a refusal at authoring. `catchTags`
takes `Cases` whose keys are all optional (`[K in E["_tag"]]+?`, `internal/effect.ts:2934`), so omitting a tag
is silently legal and the omitted error stays in `E`: safe, but you are never told. `Schema.TaggedUnion`'s
`match` looks up `cases[key]` and calls it, so a missing case is `TypeError: handler is not a function`
(`Schema.ts:6362-6366`). Our side collapses all three: `matchTag` is a `foldr` into nested `select`, each
miss typed at the residual so far, and "exhaustive" is the decidable fact `Ty.normalize residual = .never`.
A missing arm is then a refusal carrying the path (the `explain`/`blame` projection of the typing fold, DI-86),
and a redundant arm is `Ty.payloadTy tag residual = none`, so Maranget's two pattern-matrix checks read straight
off `Decision.arms`, with no new machinery.

**G3. Requirements tracking.** In rc.112 the `R` channel is a TypeScript union of service tags, discharged by
`provide`/`provideService` through `Exclude`, and there is no runtime object for it: `Effect.service(key)` on a
context that lacks the key is `Context.getUnsafe`, a **throw**, i.e. a defect
(`src/Effect4/Program/Eff.lean:350-352` transcribes exactly this from `internal/effect.ts:2059`). So a
requirements bug is a type error when inference works and a runtime defect when it does not, for instance
inside `Effect.gen`, where the inferred `R` is whatever the yields happened to union up to. On our side
`EffTy.requires` is a `Requirement` value (`src/Effect4/Program/Typing.lean:33`) with a union/diff algebra and
a `LayerTy` whose four operations are the requirement algebra of the four layer combinators (`:245-268`), and
`Closed l ↔ l.requires = Requirement.empty` (`:271`) is the decidable statement "this layer needs nothing".
That makes "what does this program need" a computed value on any subterm, printable, diffable and provable,
rather than a compiler-internal union.

**G4. The opacity of composed Schedules.** A `Schedule<Output, Input, Error, Env>` is
`Effect<(now, input) => Pull<[Output, Duration], …>>` (`Schedule.ts:250-260`), and every interesting
constructor closes over mutable JavaScript: `fibonacci` keeps `a` and `b` (`Schedule.ts:1122-1140`),
`metadataFn` keeps `n`, `previous` and `start` (`:262-275`), `exponential` reads `meta.attempt` from that
closure (`:1090-1099`). `Schedule.toStep` hands you the step function, never the state. So no consumer can ask
a composed policy whether it terminates, how many attempts it admits, or what its worst-case total delay is,
and `retry`'s own documentation has to warn you that the policy may not stop. As a data type (the select
packet's abstraction 5: `recurs n`, `spaced d`, `exponential b f`, `andThen`, `whileInput p`, `upTo n`,
`jittered`) each of those is a fold: `bounded : Schedule → Option Nat` (attempts), `maxElapsed : Schedule →
Option Nat` (worst case), `terminates : Schedule → Bool`, `print : Schedule → Tree` (the host spelling).
`jittered` (`Schedule.ts:1441-1448`) is the one arm that reads the random source, which is exactly the arm
that must become a row on the tape if a retry is to replay identically, and that is a property, not a
paragraph: a jittered schedule replayed against the same tape produces the same delays.

**G5. `Effect.gen`'s untyped yields.** `gen` takes `() => Generator<Eff, AEff, never>` and reconstructs the
error and requires channels by `[Eff] extends [Effect<infer _A, infer E, infer _R>] ? E`
(`internal/effect.ts:1183-1196`), while the iterator's own `next` is typed
`next(...args: ReadonlyArray<any>): IteratorResult<T, Success<T>>` (`Effect.ts:245-249`). Two consequences: the
value a `yield*` produces is `any` at the iterator boundary, so a wrong-typed resume is caught only by
inference at the call site; and the body is a JavaScript closure, so the program has no representation, which
means it cannot be printed, diffed, replayed, or inspected, and `Effect.fn`/`fnUntraced` inherit all of it
(`internal/effect.ts:1199-1210`). Our `Eff.gen (body : Stmts Op)` (`src/Effect4/Program/Eff.lean:316`) keeps
the generator *shape* as data with `bindYield`/`yieldDiscard`/`ret`/`ifElse`/`whileTrue`/`breakLoop` arms
(`:369-378`) and the binder row `Stmts.cons` when the head is a `bindYield` (`tools/Effect4Gen/binders.json:36`),
so each yield's answer type is the environment slot the checker assigned it. The gap on our side is the
opposite one and it is named: `gen` is `readerOnly` (`binders.json:43-45`), so nothing authors it; the plan's
target is `bind`/`select`/`iterate`, with `gen` kept only as the reader's canonical form for imported source.

**G6. Interruption regions, and the mask we cannot yet spell.** rc.112's masks are not the absolute
`uninterruptible`/`interruptible` regions our syntax has. `uninterruptibleMask(f)` passes `f` a `restore` that
is `interruptible` when the fiber *was* interruptible and `identity` when it was not
(`internal/effect.ts:4340-4352`); `interruptibleMask` is the mirror (`:4355-4367`). So `restore` means
"return to the ambient mode", a third thing, and `acquireUseRelease` (`:4201-4213`) depends on it: the `use`
runs at the caller's interruptibility, not forcibly interruptible. Our `MaskMode` already has the three values
(`src/Effect4/Machine/Supervision.lean:15`: `interruptible | uninterruptible | inherit`) but only forks read
them; the `Eff` constructors are the two absolute ones (`src/Effect4/Program/Eff.lean:323-324`). The clean
repair is to replace both constructors with one `mask (mode : MaskMode) (body)`, which is a strict
generalisation (the two old constructors are the two non-`inherit` instances, so the retirement is an
equality, exactly as `branch` retires into `select .bool`), and it unblocks `acquireUseRelease`, `onInterrupt`
and every `restore`-shaped form. The proof this buys: interruptibility is then a function of the path from
the root, so "this finalizer runs uninterruptibly" is a statement about `layerPaths`-style path folds rather
than about the interpreter.

**G7. Stream's pull-based layering, and `Done` in the error channel.** `Stream<A, E, R>` is a record holding
one `Channel<NonEmptyReadonlyArray<A>, E, void, unknown, unknown, unknown, R>` (`Stream.ts:122-127`);
`Channel` is seven type parameters (`Channel.ts:140-152`); and the thing they are both built on is
`Pull<A, E, Done, R> extends Effect<A, E | Cause.Done<Done>, R>` (`Pull.ts:39-41`), where end-of-input travels in
the *error* channel as a distinguished cause. That choice propagates: `Pull.ExcludeDone<ErrorX>` appears in
`Schedule.fromStep`'s return type (`Schedule.ts:250-256`), `retryOrElse` has to test `core.isDone(error)`
before deciding whether a failure is a failure (`internal/schedule.ts:42-46`), and every combinator that
touches a pull must be careful not to let a `Done` escape as an error. On our side termination is an arm of
the construct: the loop's exit is the loop's own decision (the `iterate` interface's two fields, select packet
§2.1), and a queue's end is a state of the queue store, not a value in the error column. What that buys is
that the error column of a streaming program means only "the program failed", so `supportedErrTy`
(`src/Effect4/Program/Eff.lean:63`) stays a closed, printable profile and the `catchIf` residual stays honest.

**G8. Where the host checker's verdict and our typing fold could disagree.** Four places, all known and all
bounded. (a) **Tag narrowing.** `Ty.taggedColumn` (`src/Effect4/Program/Ty.lean:599`) is the exact condition
under which `payloadTy`/`diffTag` agree with `Extract`/`Exclude`; off that column TypeScript narrows
structurally (any object with a `_tag`) and we refuse. We are stricter, which is the safe direction, but the
boundary must be a printed-and-checked row (the select packet §1.8 controls under strict type-check).
(b) **Answer joins.** We join answers as the canonical union least upper bound (`EffTy.joinAnswer`,
`src/Effect4/Program/Typing.lean:40-44`); TypeScript's union of two branch results is subject to literal
widening, `Unify`, and excess-property rules, so a program we type at `"A" | "B"` can be typed by `tsgo` at
`string`. (c) **Requirements.** Our `Requirement.diff` is set difference on keys; TypeScript's is `Exclude` on
a union of tag *types*, which collapses two distinct keys with the same type. (d) **Literal rule.** Our error
profile admits a tagged pair only when both components are string-valued (`rawSupportedErrTy`,
`src/Effect4/Program/Eff.lean:55-60`); rc.112 admits any object. The mechanism that keeps these honest is the
one already in place: every printed row goes through the host checker's lane (R0) and a row `tsgo` refuses is
an import defect, so disagreement surfaces as a red lane rather than as a silent divergence.

**G9. Our own gap: `catchIf` has no miss arm.** rc.112's `catchIf` is *three*-armed,
`catchIf(self, predicate, f, orElse?)`, where a miss runs `orElse(error)` when it is supplied and re-raises the
whole cause when it is not (`internal/effect.ts:2796-2810`), and `catchFilter` is the same with a `Filter` in
place of the predicate (`:2814-2846`). Our `Eff.catchIf (test) (body) (handler)`
(`src/Effect4/Program/Eff.lean:356-360`) only has the hit arm; a miss retains the cause. That means
`catchTags` with an `orElse`, `catchReason` and every three-armed recovery cannot be written today. The repair
is the same move `select` made on `branch`: `catchOn (decision : Decision) (body hit miss)`, where `decide`
runs on the first represented error and the miss arm binds the residual error: one constructor,
`catchIf` retiring into it as the `.bool`-with-a-test instance, and `catchIfError`
(`src/Effect4/Program/Typing.lean:327`) generalising to `Decision.arms` on the error column.

**G10. `Filter`'s types are hand-written.** `Filter.compose`'s declared result is
`Filter<InputL, PassR, FailL | FailR>` (`Filter.ts:1085`) and its body is four lines of `Result` plumbing
(`:1089-1096`); nothing checks the two agree, and the same is true of `or` (`:714`), `zipWith` (`:755`),
`andLeft` (`:907`), `andRight` (`:973`) and `composePassthrough` (`:1108`). Ours is the opposite by
construction: a `Decision` combinator defines `decide` and `arms` from its children's, and `decide_typed`
extends by one case. Six combinators, six proof cases, and a whole family of narrowing bugs cannot exist.

**G11. Nine exports that are one rewrite.** `mapEager`, `flatMapEager`, `mapErrorEager`, `mapBothEager`,
`catchEager`, `matchEager`, `matchCauseEager`, `matchCauseEffectEager`, `fnUntracedEager` differ from their
plain twins only by `if (effectIsExit(self))` (`internal/effect.ts:1741-1744`, `:1789`, `:3573` onward,
`Effect.ts:25016-25649`). The optimisation is real and the API cost is nine names a reader must learn and
choose between. On our side `succeed`/`fail`/`failCause` are already the exit-shaped nodes, so the same
optimisation is a peephole `AlgMap` over `Eff` (`bind (succeed v) rest ↦ rest[v/0]`,
`catchCause (succeed v) h ↦ succeed v`) applied through `cata_eff` with one theorem that `meaning` is
preserved. One transform, one proof, zero new names.

**G12. Three do-notations and two result carriers.** `Effect` has `Do`/`bindTo`/`bind`/`gen`
(`internal/effect.ts:5175-5191`, `:1175`), `Option` has its own `Do`/`bind`/`bindTo`/`gen`
(`Option.ts:4268`, `:4171`, `:4027`, `:4305`), `Result` has a third set (`Result.ts:2838`, `:2875`, `:2985`,
`:2784`). Each is the same encoding of a named-slot environment as a record, spelled three times, and none of
them is the program's real binding structure. Our positional environment (decision D1,
`src/Effect4/Program/Eff.lean:19-22`) *is* that record: `bind answer first rest` names the slot, `Src`'s
`env.push` is `bindTo`, and one binder table (`tools/Effect4Gen/binders.json`) says what every construct binds.
So the three notations are one `eff` notation over one binder table, and `Option`/`Result` elimination is a
`Decision`, not a monad.

**G13. `dual`'s runtime dispatch, already data on our side.** Every second export is wrapped in `dual`, which
decides data-first from data-last either by arity or by a *runtime predicate on the arguments*:
`dual((args) => isEffect(args[0]), …)` for `catchIf` (`internal/effect.ts:2795`),
`dual((args) => typeof args[1] === "function", …)` for `forEach` (`:4671`),
`dual((args) => isIterable(args[0]) && !isEffect(args[0]), …)` for `partition` (`:4436`). That dispatch is
undocumented per-export behaviour in TypeScript; our reader already reifies it as an enum with five rules
(`Codegen.Forms.DualRule` and `Forms.duals`, `src/Effect4/Codegen/Forms.lean:151-164`). Keep it and grow it:
it is the right shape and it is the only place in the estate where `dual` is a fact rather than a convention.

**G14. `unassigned` as a type-level sentinel.** `catchIf`, `catchFilter`, `catchTag` and `catchTags` all thread
`A3 = unassigned` and then test `A3 extends unassigned ? … : never` to decide whether the caller supplied an
`orElse` (`Types.ts:873`, `internal/effect.ts:2761-2768`). It works and it is unreadable, and it exists only
because an optional argument has to change the *result* type. In a data language the optional arm is a
constructor field, and its absence is a different node.

**G15. One entry shape, spelled four times.** §2.11 above. What our side adds is that the entry is the same
object as the row a program performs, so the tool table a model reads, the OpenAPI document a client reads,
the row a program performs, and the tape line a replay checks are four projections of one document
(`Schema/Bridge.lean:162` already projects `EffTy → Document`).

## 6. What would need a new core construct

Three, with their cost. The rule the estate applies (owner's steer, top of the abstraction tree) is that a new
`Eff` constructor costs roughly the 71 lines in 18 files that the select packet measured for `branch`
(`docs/research/2026-09-16-select-and-iterate-ready-packet.md` §0), plus a wire tag, plus a generator arm, plus
a lemma family per fold. So the bar is high and only the first of these three clearly clears it.

**C1. `mask (mode : MaskMode) (body)` replacing `uninterruptible` and `interruptible`.** *Worth it.*
Justification is G6: `restore`-to-ambient is a real mode rc.112 depends on for `acquireUseRelease`,
`onInterrupt` and every `*Mask`, and we cannot express it. Cost is unusually low because it is a *merge*, not
an addition: two constructors become one with a three-valued field, the two old forms are two instances so
every existing arm reduces by `cases mode`, the wire loses a tag rather than gaining one, and `MaskMode`
already exists with its `cases_receipt` (`src/Effect4/Machine/Supervision.lean:15`, `:79`). Net constructor
count falls by one.

**C2. A first-to-exit race.** *Probably a field, not a constructor.* `timeout`, `timeoutOption` and
`timeoutOrElse` are all `raceFirst(self, flatMap(sleep(d), orElse))` (`internal/effect.ts:3700-3703`), and
`raceFirst`/`raceAllFirst` differ from `race`/`raceAll` only in whether the first *failure* wins or is
collected (`:1535-1581` against `:1477-1533`). We model the first-success variant
(`ActionTerm.raceAll`, `src/Effect4/Program/Eff.lean:400`; witness
`src/Effect4/Laws/Machine/Witnesses.lean:386`, with the all-failed ordering fixture at `:438`). The cheap
answer is a Boolean or a two-valued mode on `ActionTerm.raceAll`, since the entrant list, the fork set and the
interrupt-the-losers step are identical and only the `onExit` arm differs. That costs one field on an existing
`ActionTerm` constructor and one extra case in the race clause (`src/Effect4/Laws/Machine/Clauses.lean:1615`).
Do not add a constructor for it.

**C3. A memoised suspension keyed by path.** *Defer; write the design down.* `Effect.cached` has type
`Effect<A, E, R> => Effect<Effect<A, E, R>>` (`internal/effect.ts:4291`), and `cachedWithTTL`/
`cachedInvalidateWithTTL` add a clock and an invalidation handle (`Effect.ts:13869`, `:14036`). A program that
yields a program is outside a first-order language by construction. But the *mechanism* is one we already own:
a layer's identity is its path in the program and rc.112 keys its memo map on the layer object
(`src/Effect4/Program/Eff.lean:405-413`, citing `Layer.ts:411`, `:438`), which is exactly "memoise this
subterm, keyed by where it is". Generalising the layer memo map to an arbitrary subterm gives `cached` without
a program-valued type: `memo (body)` runs `body` at most once per path per run and answers from the memo store
afterwards. Cost: one constructor, one store family, a TTL variant that needs the clock, and, the expensive
part, a meaning equation that has to talk about the memo store, so `Straight` would exclude it and the
straight-fragment theorems would not cover it. Recommendation: not now; note it, and use a `Deferred` plus a
`Ref` (both already rows, `src/Effect4/Program/Native.lean:102-120`) as the hand-written idiom, which is what
`cachedWithTTL` itself does under the hood.

**What does *not* need a constructor, despite looking like it does.** A `Decision` on the error channel (G9:
a field on `catchIf`, or `catchOn` replacing it, which is again a merge). `forEach`/`all` with concurrency (a
fold over `withFiber` plus a semaphore row). `Schedule` (a data type outside `Eff`, folded into `iterate`).
`Queue`/`PubSub`/`Semaphore`/`Latch` (rows over new store families; the machine's park/wake list is already
generic, `src/Effect4/Machine/Wake.lean`). `Stream` (sugar over a queue row and `iterate`). `Config` (a data
type outside `Eff` whose `parse` is a fold into rows). `Match` (nested `select`). Every `*Eager` (a rewrite).

## 7. Addendum A: the building blocks of robust concurrent software

Owner's addendum of 2026-09-16: beyond sugar, each of these should be trivial and composable on our side, a
fold over what we already have (`Deferred`, `Latch`, `Semaphore`, `Scope`, fork, `catchIf`, `iterate`,
`select`, the tape) or, if truly needed, one new native row. Same classification vocabulary as §2. "The proof"
column names the specific thing the machine could give, in the estate's evidence words: a **tape property**
(checkable by `Api.replay`/`replaySteps`/`Run.trace`, `src/Effect4/Api.lean:275`, `:355`, `:326`), a **store
invariant** (a theorem about a store family across every reachable state), or a **theorem over `denote`**
(an equation on the meaning fold).

| # | pattern | what rc.112 offers (cite) | what it lacks | the fold on our side | the proof the machine could give |
| --- | --- | --- | --- | --- | --- |
| A1 | true concurrency, structured interruption, cancellation propagation | `forkChild`/`forkIn`/`forkScoped`/`forkDetach` `Effect.ts:16990`-`17168`; `Scope` `Scope.ts:215`; `uninterruptibleMask`/`interruptibleMask` `internal/effect.ts:4340-4367`; `Fiber.interrupt*` `Fiber.ts:354`, `:527`; `awaitAllChildren` `Effect.ts:17207` | `restore` is a closure, so an interruptibility region is not inspectable; no way to ask "is this node interruptible"; children are tied to scopes only by the fork option that built them | `withFiber (.fork …)` + `scoped` + `mask` (C1) + `awaitFiber`; all four already constructors (`src/Effect4/Program/Eff.lean:337`, `:339-342`, `:389`) | **tape property**: every forked child appears in `Run.trace` and is interrupted before its scope's finalizers; **theorem over `denote`**: interruptibility at a node is a function of the path from the root once `mask` replaces the two absolute regions |
| A2 | deadlines and timeouts | `timeout`/`timeoutOption`/`timeoutOrElse` = `raceFirst(self, sleep(d) >>= orElse)` `internal/effect.ts:3677-3727` | no ambient deadline a child inherits, so every timeout is a fresh race and nested calls each restart the clock; `raceFirst` is not `raceAll` (our gap, §6 C2) | `raceAll` with a first-to-exit field + the `sleep` row (`src/Effect4/Program/Native.lean:125`); an ambient deadline is `provideService` of a deadline value read by the sugar | **tape property**: with a synthesised clock tape (`src/Effect4/Api/TestClock.lean:38`) the timeout fires at exactly the modelled millis; **store invariant**: a timed-out body's fiber is not live after the race resolves |
| A3 | state machines with typed transitions | nothing in the standard modules; `Schedule`'s step function `Schedule.ts:250`; `unstable/cluster/Entity.ts`; `unstable/workflow/Workflow.ts:429` (durable, suspendable executions) | transitions are closures; no reachability, determinism or exhaustiveness check; a machine cannot be printed or diffed | already done once (dogfood 6, 2026-09-16): a machine is a row table `(state, event, guard, target, action)` compiled by a fold into `iterate` over the state cursor with `matchTag` on the event | **theorem over `denote`**: `compile_run_eq_meaning` per model, already proved for the vendored statechart library; determinism is "at most one guard hits", which is `Decision.arms` exhaustiveness; unreachable states are a fold over the table |
| A4 | streams: backpressure, batching, chunking, graceful end | `Queue.make({capacity, strategy})` with `"suspend" \| "dropping" \| "sliding"` `Queue.ts:448-467`; `Queue.State` `Open \| Closing \| Done` `Queue.ts:343-360`; `Queue.end` `:1058`; `Stream` chunks by construction `Stream.ts:123`; batching `RequestResolver.batchN` `RequestResolver.ts:1019` | end-of-input rides the error channel at the `Pull` layer (`Pull.ts:39`), so every downstream signature carries `ExcludeDone`; the backpressure invariant is prose | one queue store family (counter, capacity, a three-valued strategy, a three-valued state, two `WakeList`s, where `src/Effect4/Machine/Wake.lean:119` is already the generic park list); `offer`/`take`/`takeN`/`end`/`fail` as rows; a stream is `iterate` over `take` with a `.option` decision for the end | **store invariant**, one per strategy: `suspend` never exceeds capacity and loses nothing, `dropping` drops exactly the newest, `sliding` drops exactly the oldest; **tape property**: a consumer that runs to `end` sees every offered value once, in order |
| A5 | observability: spans, metrics, logs as data | `Tracer.Span` with `end`/`attribute`/`event` `Tracer.ts:372-388`; `withSpan`/`makeSpanScoped` attach the end to a scope finalizer `internal/effect.ts:5798-5813`; `Metric` carries `id`/`type`/`description`/`attributes` as data plus `updateUnsafe` `Metric.ts:111-123`; `Logger` `Logger.ts:64`; OTLP exporters `unstable/observability/Otlp*.ts` | spans and metrics are side effects into services; the span tree cannot be recovered from the program, and nothing ties span nesting to program nesting | a span is `scoped` plus two rows (start, end); a metric update and a log line are rows; the declaration side (`id`, `type`, `description`, `attributes`) is data beside the row exactly as `Row` already is | **theorem over `denote`**: the span tree equals the scope tree of the program (a path fold, the same shape as `layerPaths`); **tape property**: every started span is ended, because the end is a scope finalizer; metric monotonicity is a **store invariant** |
| A6 | message passing: mailboxes, request/response, fan-out | `Queue` `Queue.ts:448`; `PubSub.subscribe` returning a scoped `Subscription` `PubSub.ts:1304`, `:236`; `Deferred.make`/`await` `Deferred.ts:171`, `:173-186`; `Request`/`RequestResolver` `Request.ts:293`, `RequestResolver.ts:236` | fan-out under a full bounded `PubSub` differs per strategy and is documented, not stated; nothing says a subscriber sees a prefix | `Deferred` rows already exist (`src/Effect4/Program/Native.lean:115-120`); a mailbox is the queue row family of A4; pubsub is that store plus one cursor per subscriber | **store invariant**: a subscriber's takes are a contiguous run of the publishes after its subscribe; **store invariant** (already our deferred laws' shape): every `deferredAwait` is woken by exactly one completion |
| A7 | config and env access | `Config<T> extends Effect<T, ConfigError>` with `parse(provider)` `Config.ts:108-112`; `map`, `mapOrFail`, `orElse`, `withDefault`, `option`, `nested`, `Record` `Config.ts:252`-`1943`; `ConfigProvider`; `Flag.withFallbackConfig` `unstable/cli/Flag.ts:872` | a `Config` is a closure over `parse`, so the keys a program reads cannot be enumerated, documented or templated; the internal `Resolution`/`Absent` machinery (`Config.ts:117-135`) exists only because the Effect error channel cannot distinguish absent from failed | a `Config` data type (`key`, `schema`, `default?`, `nested`, `map`, `orElse`) outside `Eff`, with `keys : Config → List Path` a fold and `compile : Config → Eff` a fold into provider rows; absent-versus-failed is `Decision .option` on the read | **theorem over `denote`**: `keys` is complete, so every provider row the compiled program performs reads a key in `keys`; the parsed value inhabits the declared schema by the bridge retraction (`src/Effect4/Schema/Bridge.lean:114`) |
| A8 | at-least-once / at-most-once delivery | `MessageStorage.SaveResult` `unstable/cluster/MessageStorage.ts:213`; `PersistedQueue` with id-based de-duplication and retry `unstable/persistence/PersistedQueue.ts:1-12`; `WorkflowEngine.activityExecute` journalling `unstable/workflow/WorkflowEngine.ts:146` | the guarantee belongs to the storage implementation and is stated in prose; nothing checks a handler is safe to run twice | the tape *is* the journal: an at-least-once step is a row whose answer is recorded and re-answered on replay; at-most-once is a row preceded by a de-dup read and a `Decision` | **tape property**: `Tape.Complete` (`src/Effect4/Api.lean:288`) already says no host reply is outstanding and no decision is missing; delivery is "replaying the same tape yields the same `Run.exit` and the same external requests", checkable per decision through `replaySteps` (`:355`) |
| A9 | idempotency keys | `Activity.idempotencyKey(name, {includeAttempt})` = hash of `executionId[-attempt]-name` `unstable/workflow/Activity.ts:255-270`; `Tool.Idempotent` annotation `unstable/ai/Tool.ts:1857` | the key is computed by a host function inside a `gen`; nothing relates it to the program's structure, and two call sites sharing a `name` collide silently | the key is the node's **path**, which we already have as a value (`LayerTerm.ref` keys the memo map on a path, `src/Effect4/Program/Eff.lean:437`, citing `Layer.ts:411`, `:438`), plus the run id and, inside a loop, the `iterate` cursor. A derived term, not a row | **theorem over `denote`**: paths are unique per node by construction (`layerRefsWF` in `src/Effect4/Program/Refs.lean` is the existing precedent), so two distinct steps never share a key without a hash-collision assumption |
| A10 | fencing tokens and leases | `Sharding` acquires and releases shard locks via `runnerStorage.release`/`releaseAll` with a forced-release path `unstable/cluster/Sharding.ts:287-361`; `Snowflake` gives monotone ids carrying timestamp, machineId and sequence `unstable/cluster/Snowflake.ts:161-209` | no first-class lease; the fence is implicit in the storage protocol, and the "forced release wipes a lock" hazard is handled by a comment and a mutable flag (`Sharding.ts:356-360`) | `acquireRelease` over a lease row whose answer is a token, the token threaded as a term into every guarded row; fencing is a `Decision` comparing the carried token with the store's current one, so a stale writer takes the miss arm | **store invariant**: no two holders of one lease are live at once; **theorem over `denote`**: every guarded row carries the token bound by the enclosing `acquireRelease`, a scope-safety statement of exactly the shape `scopedAlgebra` already proves (48 generated lift lemmas, scope-safety landing) |
| A11 | outbox and inbox | `PersistedQueue` is documented for "outbox-style integrations" `unstable/persistence/PersistedQueue.ts:6`, with memory, Redis and SQL stores `:290`, `:365`, `:753`; `MessageStorage` is the cluster inbox `unstable/cluster/MessageStorage.ts:213` | the transactional coupling of the business write to the outbox write is left to the caller; no type says two rows are in one transaction | both rows inside one transaction region over the SQL package (`src/Effect4/Program/Packages.lean:33-38`); the inbox is a de-dup store read by a `Decision` before the handler | **tape property**: the outbox row is performed if and only if the business row is; a crash is a truncation of the tape, and replay resumes at the same frontier (`replaySteps`) |
| A12 | sagas with compensation | `Workflow.withCompensation(effect, compensation)`, the compensation running if the *whole workflow* fails `unstable/workflow/Workflow.ts:831-881`; locally `onExit`/`acquireRelease` `internal/effect.ts:4032`, `:3971` | the compensation list is built at runtime inside the engine; order and guarantee are invisible in the type; `onExit` is per-step so it cannot express "undo in reverse on a later failure" | a saga is a list of `(step, compensation)` folded into nested `acquireRelease` whose release is the compensation guarded by a `Decision .exit`, and our `acquireRelease`'s release already sees both the resource and the exit (`tools/Effect4Gen/binders.json:33`) | **theorem over `denote`**: on a failure at step k, compensations k-1…0 run in reverse order and each sees its own resource, proved once about the nested fold, for every saga |
| A13 | circuit breakers | **nothing**: `grep -ri 'circuit.?breaker'` over the whole pinned `src` matches no file. Nearest is `ExecutionPlan`'s per-step `attempts`/`while` `ExecutionPlan.ts:100-110`, which is a fallback ladder | the pattern is absent | A3 applied to one row: a three-state store (closed/open/half-open), a `Decision .tag` on the state before the call, a `catchIf` counting failures into the store, `iterate` for the half-open probe | **tape property**: while the breaker is open no guarded row is performed; **store invariant**: it opens after exactly n consecutive failures |
| A14 | bulkheads | `Semaphore.withPermits` `Semaphore.ts:447`; `PartitionedSemaphore.withPermits` `PartitionedSemaphore.ts:557`; `Pool` `Pool.ts:232`; `forEach`'s `concurrency` `internal/effect.ts:4683` | no name for the pattern and no statement of the isolation property | one semaphore store, a counter plus a `WakeList` (rc.112's own `SemaphoreImpl` is exactly `{permits, taken, waiters}`, `Semaphore.ts:225-233`, with the parked-waiter callback at `:207-223`), used under `acquireRelease` over `take`/`release`; partitioned is the same store keyed | **store invariant**: at most n fibers inside the region at once, one theorem serving every bulkhead |
| A15 | hedged requests | no hedging combinator. `race`/`raceAll` `internal/effect.ts:1477`, `:1583` duplicate unconditionally; `ExecutionPlan` `ExecutionPlan.ts:169` is sequential fallback | the delayed second attempt must be hand-written at each site | a form, no new anything: `raceAll [body, bind (perform sleep d) body]` over `ActionTerm.raceAll` (`src/Effect4/Program/Eff.lean:400`) and the `sleep` row | **tape property**: at most two requests issued; the loser is interrupted, which is the existing race clause (`src/Effect4/Laws/Machine/Clauses.lean:1615`) |
| A16 | retry with jitter | `Schedule.jittered` multiplies the delay by a uniform factor in [0.8, 1.2] drawn from `randomNext` `Schedule.ts:1441-1448`, `:30` | the draw is on no tape, so a jittered retry cannot be replayed; and the schedule's opacity (G4) means the total wait cannot be bounded | `jittered` as an arm of the schedule data type; the draw is a row, so it lands on the tape like every other answer | **tape property**: same tape, same delays; **theorem over `denote`**: `maxElapsed (jittered s) ≤ 1.2 × maxElapsed s`, a fold-level lemma |
| A17 | supervision trees and restart policies | `forkChild`/`forkScoped`/`forkIn`/`forkDetach` set the parent scope `Effect.ts:16990-17168`; `FiberHandle`/`FiberMap`/`FiberSet` with `run`, `clear`, `join`, `awaitEmpty` `FiberHandle.ts:709`, `:1012`, `:1041`, `FiberMap.ts:1268`, `FiberSet.ts:606`; `Singleton.make` `unstable/cluster/Singleton.ts:46` | no restart policy as a value; "restart this child with this schedule on this class of failure" is hand-written each time; the supervision tree is not a printable value | the tree *is* the program's fork paths, already data; a restart policy is a `Schedule` plus a `Decision` on the child's exit folded into `iterate` around the fork; a `FiberMap` is a handle store keyed by a term | **theorem over `denote`**: every child is a descendant of the scope it was forked in, a path fold over `ForkOptions` (`src/Effect4/Machine/Supervision.lean:20`); **tape property**: a supervised child is restarted at most n times |
| A18 | rate limiting | `unstable/persistence/RateLimiter` with fixed-window and token-bucket algorithms over a shared store, memory and Redis layers `RateLimiter.ts:86`, `:226`, `:695`, `:1355`, plus `ConsumeResult` and an adaptive variant `:488`, `:526` | the two algorithms are hand-written per store; "no more than n per window" is stated nowhere | one store (counter plus window start, or token count plus refill time), one `consume` row, a `Decision` on the result, `iterate` + `sleep` for the waiting variant | **tape property**: at most n rows performed in any window of length w, proved once per algorithm |

**What this table says as a whole.** Fourteen of the eighteen need *no new `Eff` constructor at all*: they are
store families plus rows plus folds. Three want the `mask` merge of §6 C1 (A1, A2, A12, indirectly), one wants
the race field of §6 C2 (A2), and none wants a genuinely new construct. The reason is structural rather than
lucky: every one of these patterns is (i) a small piece of state with parked waiters, which is our store plus
`WakeList`; (ii) a decision on that state, which is `Decision`; (iii) a loop, which is `iterate`; and (iv) a
region with a finalizer, which is `scoped`/`acquireRelease`. That is the whole kit, and it is the honest answer
to "what would make robust concurrent software trivial on our side": finish `iterate`, add the `Decision`
constructors of §4, add the queue and semaphore store families, and everything above is a definition in
`Authoring/Sugar.lean` with a named proof obligation.

## 8. Addendum B: result types and the plumbing around them

Owner's second addendum. For each: the Effect form with its citation, our form today or the gap, and the `eff`
notation line.

### B1. Result types as values, and consuming them back

| Effect form | pinned | what it is | our form today | `eff` line |
| --- | --- | --- | --- | --- |
| `Effect.exit` | `internal/effect.ts:3621-3637`, a **primitive** (`op: "Exit"`) that pushes a frame catching both continuations | success or failure as one value | `Eff.exit (body)` (`src/Effect4/Program/Eff.lean:321`), primitive `Prim.exitFrame`; the answer type is `.exitOf b.answer b.error` (`src/Effect4/Program/Typing.lean:350`) | `let e ← exit do body` |
| `Effect.result` (rc.112's `either`; there is **no** `Effect.either`, and no `Either` module) | `internal/effect.ts:3417-3420` = `matchEager(self, {onFailure: Result.fail, onSuccess: Result.succeed})` | typed failure or success, defects still propagating | **gap, sugar**: `matchCause body (succeed (ok v)) (succeed (err e))`, or once `.exit` lands, `bind (exit body) (select (var 0) .exit …)`. The answer type `Ty.result` already exists as an abbrev for `except` (`src/Effect4/Program/Ty.lean:49`) | `let r ← result do body` |
| `Effect.option` | `internal/effect.ts:3412-3414` = `match(self, {onFailure: Option.none, onSuccess: Option.some})` | success or nothing | **gap, sugar**: same fold with `.option`; `Ty.option` exists (`Ty.lean:31`) | `let o ← option do body` |
| consuming them back: `Option.match`, `Result.match`, `Exit.match` | `Option.ts:403`, `Result.ts:1182`, `Exit.ts:752` | three eliminators, three modules | **this is where `select` lands**: `.option` exists today (`src/Effect4/Program/Decision.lean:36-48`); `.result` and `.exit` are §4's first two rows | `match r with | err e => … | ok v => …` |
| `Exit.filterSuccess`, `filterValue`, `filterFailure`, `filterCause`, `findError`, `findDefect` | `Exit.ts:545`, `:582`, `:616`, `:651`, `:686`, `:721` | six `Filter`s over an exit | one `.exit` decision plus one `.cause` decision (§4) | `match e with | failure c => … | success v => …` |
| `Effect.transposeOption`, `fromOption`, `fromResult`, `fromNullishOr` | `Effect.ts:2509`, `:2462`, `:2423`, `:2538` | moving between the value and the error channel | sugar: `select` on the value, then `fail`/`succeed` | `match o with | none => fail e | some v => pure v` |
| `Effect.isSuccess`, `isFailure` | `Effect.ts:11200`, `:11230` | Boolean projections of an exit | sugar over `.exit` then `succeed (bool …)` | (none needed) |
| `Effect.sandbox` | `internal/effect.ts:1472-1474` = `catchCause(self, fail)` | the cause moved into the error channel | **out of scope today**: our error language is a closed profile (`rawSupportedErrTy`, `src/Effect4/Program/Eff.lean:55-60`) and a cause is not in it; `.causeOf` exists as a `Ty` (`Ty.lean:38`) so the repair is to admit it in the answer channel, via `matchCause`, not the error channel | `let c ← cause do body` |

The shape of the answer here: rc.112 makes `exit` the primitive and derives `option` and `result` from it (two
of three are `match` folds). We do the same and get the *elimination* for free, because `select` with `.exit`
and `.result` is one constructor with two more decisions rather than two more modules with their own `Do`,
`bind`, `gen`, `map`, `flatMap`, `zipLeft`, `zipRight`, `tap`, `all`, `product` and `liftPredicate`
(`Option.ts` is 4437 lines and `Result.ts` 3400 lines, most of it that duplication).

### B2. `flatMap` versus `map` versus `andThen` versus `tap`, and the discarding forms

| Effect form | pinned | our form today | `eff` line |
| --- | --- | --- | --- |
| `flatMap(self, a => f(a))` | `internal/effect.ts:1590` | `Eff.bind first rest`, with the answer bound as the next variable; sugar `flatMap` (`src/Effect4/Program/Authoring/Sugar.lean:30`), binder row `bind` (`tools/Effect4Gen/binders.json:24`) | `let x ← e` |
| `map(self, a => b)` | `internal/effect.ts:1759` | sugar `map atom e` = `bindWith e (fun v => succeed (app atom [v]))` (`Sugar.lean:36`); note the function must be an **atom name**, never a Lean closure | `let x ← e; pure (f x)` |
| `andThen(self, f)` where `f` is an effect *or* a function, dispatched at runtime by `isEffect(f)` | `internal/effect.ts:1432-1439` | three forms, one per shape: `"andThenEffect"`, `"andThenContinuation"`, `"andThenThunk"` (`src/Effect4/Codegen/Forms.lean:93-98`); sugar `andThen` binds the name `"_"` (`Sugar.lean:33`) | `e₁; e₂` |
| `tap(self, f)` = `flatMap(self, a => as(f(a), a))` | `internal/effect.ts:1457-1464` | forms `"tapContinuation"`, `"tapEffect"` (`Forms.lean:103-106`) | `tap e with v => k` |
| `as(self, value)` = `flatMap(self, _ => succeed(value))` | `internal/effect.ts:1396-1399` | form `"as"` (`Forms.lean:99`) | `e as v` |
| `asVoid(self)` = `flatMap(self, _ => exitVoid)` | `internal/effect.ts:1467-1469` | form `"asVoid"` (`Forms.lean:101`) | `e as ()` |
| `ignore(self)`, `ignoreCause(self)` | `internal/effect.ts:3333`, `:3376` | **gap, sugar**: `matchCause e (succeed unit) (succeed unit)` | `ignore e` |
| `zip`, `zipWith` sequential | `internal/effect.ts:2307` = `flatMap(self, a => map(that, a2 => f(a, a2)))` | **gap, sugar**: `bind a (bind b (succeed (app atom [var 1, var 0])))` | `let x ← a; let y ← b; pure (f x y)` |
| `zipLeft`, `zipRight` | **absent on `Effect` in rc.112** (`grep -c` over `Effect.ts` and `internal/effect.ts` returns 0); they survive only on `Option` (`Option.ts:2308`, `:2397`) | nothing to mirror; `andThen` and `tap` cover both directions | (none needed) |
| the discarding binder | `Effect.gen` bodies write `yield* e` with no `const` | `Stmt.yieldDiscard` (`src/Effect4/Program/Eff.lean:373`) in generator bodies; in `bind` form, `Sugar.andThen` with the name `"_"` (`Sugar.lean:33`) | a bare `e` line, no `let` |

One honest wrinkle on our side: `andThen` binds the *literal* name `"_"` rather than a minted fresh one, while
`bindWith` mints `"_" ++ toString env.names.length` (`Sugar.lean:25-28`). Two nested `andThen`s therefore both
introduce the spelling `"_"`, and an author who writes `var "_"` resolves to the nearest one. It is not a
soundness problem, since the tree is positional and the elaborated program is correct either way, but the `eff`
notation should use the minting form so that a discarded slot has no addressable spelling at all.

### B3. `flatten`, and why the first-order form is the right one

`Effect.flatten : Effect<Effect<A, E, R>, E2, R2> => Effect<A, E | E2, R | R2>` is `flatMap(self, identity)`
(`internal/effect.ts:1754-1756`). A program that is a *value* is outside our language by construction: `Ty`
(`src/Effect4/Program/Ty.lean:23-43`) has no program constructor, and decision D1
(`src/Effect4/Program/Eff.lean:19-22`) says a program carried by anything is an `Eff` subterm, never a value.
So the classification is **out of scope as a value**, and the three real uses split cleanly:

- *The inner program is literally known.* `flatten(succeed(p))` is `p`. In our tree that is not even a rewrite:
  you wrote `p`.
- *The inner program is chosen by a condition.* `flatten(map(cond, b => b ? p : q))` becomes
  `select cond .bool p q`. The choice of program moves from a value to a fork, which is the whole point of
  `select`: a dynamic choice among a **finite, written-down** set of continuations.
- *The inner program is genuinely computed by the host* (`cached`, a resolver that returns an effect, a plugin).
  That is §6 C3 and the external row: the host computes it, and what crosses the boundary is an answer on the
  tape, not a program.

`eff` line: there is none, and that is the point. `flatten` has no spelling because a program is never in a
term position.

### B4. Eager versus lazy construction, and how the image and the machine keep the distinction

| Effect form | pinned | what is deferred | our form | how the distinction is kept |
| --- | --- | --- | --- | --- |
| `succeed(value)` | `Effect.ts:1437`; the result satisfies `effectIsExit` (`internal/effect.ts:1742`) | nothing: the value is already in hand and the node *is* an `Exit` | `Eff.succeed (value : Term)` (`src/Effect4/Program/Eff.lean:306`), a **term** evaluated at the node's environment | printed as `Effect.succeed(t)`; compiled to `Prim.success` (the `arms` row, `Eff.lean:518`); `denote` evaluates the term once |
| `sync(thunk)` | `internal/effect.ts` `op: "Sync"`; `Effect.ts:1607` | a JavaScript thunk, arbitrary host code | `Eff.sync (thunk : Term)` (`Eff.lean:311`), a term over the closed `NativeAtom` table, not a closure | printed as `Effect.sync(() => t)`; compiled to `Prim.sync` (the `arms` row, `Eff.lean:522`). **The narrowing is deliberate**: arbitrary host code is what the external row is for |
| `suspend(() => effect)` | `internal/effect.ts:939-945`, a primitive whose `evaluate` calls the thunk | a whole program, deferred to force time | `Eff.suspend (body : Eff Op)` (`Eff.lean:312`), where the body is a **subterm**, so nothing is deferred at the data level; the deferral is the machine's (`compileEff` emits `Prim.suspend`) | printed as `Effect.suspend(() => p)`; the machine forces it at `suspendBodyAt` |
| `promise(evaluate)`, `tryPromise` | `internal/effect.ts:1051-1060`, `:1062` | a host promise, resolved through `callback` | an **external row** (`registration := .external`, `kind := .async`, `src/Effect4/Program/Native.lean:130`, `:359-367`), answered by the tape on replay | the row is data; the answer is a tape line |
| `cached`, `cachedWithTTL`, `cachedInvalidateWithTTL` | `internal/effect.ts:4291`; `Effect.ts:13869`, `:14036` | the *result* of a program, memoised, handed back as a program | **gap**, §6 C3. The idiom today is a `Deferred` plus a `Ref`, both already rows (`Native.lean:102-120`), which is what `cachedWithTTL` itself does underneath | (none yet) |
| layer memoisation | `Layer.ts:411`, `:438`, where the memo map is keyed on the layer *object* | the built service, once per memo map | already ours: a layer's identity is its **path**, and a second occurrence is `LayerTerm.ref target` (`Eff.lean:437`) | the path is in the data; the memo key is derivable from the program, not from object identity |

The rule this table makes explicit, and which the `eff` notation should honour: **in our language laziness is
never a closure, it is a position in the tree.** `succeed` takes a term because the value is available at the
node's environment; `sync` takes a term because the host computation we admit is exactly the atom table;
`suspend` takes a subterm because the deferral is the machine's job, not the syntax's; and everything that
genuinely needs host laziness is an external row whose answer is on the tape. That is why our printed image can
round-trip (`roundTrip nativeSignature nativeSpell`, `src/Effect4/Codegen/Forms.lean:194`) while a
closure-carrying `Effect` cannot.

### B5. Sequencing with discard in generator bodies

`Effect.gen` bodies discard with a bare `yield* e` (no `const`), and rc.112 types the generator as
`Generator<Eff, AEff, never>` (`internal/effect.ts:1182`) so the discarded answer has no name at all. Our
`Stmt` family already distinguishes the two (`src/Effect4/Program/Eff.lean:371-373`: `bindYield` binds the
answer as the next variable, `yieldDiscard` does not), and the binder table encodes exactly that: the
`Stmts.cons` row extends the scope only `whenHead` is `Stmt.bindYield` (`tools/Effect4Gen/binders.json:36`).
That is the one place in the estate where a per-head binder rule already existed before `select` needed it,
and it is the right precedent: the discard is a *different constructor*, not a magic name.

`eff` lines: `let x ← e` for the binding form, a bare `e` on its own line for the discard, and one thing to
add: `let _ ← e` should elaborate to `yieldDiscard`/`andThen` rather than to a binder named `_`, so that
"discarded" is a fact about the tree and not about a spelling.

## 8b. An unasked-for finding: the `arms` table's citations have drifted off the pin

Not part of the brief, but it fell out of checking every citation I used. `src/Effect4/Program/Eff.lean:517-545`
is the `arms` table, one row per constructor naming the rc.112 combinator and the line it transcribes, with the
header rule "`vendor/effect-4.0.0-rc.112/src/internal/effect.ts` unless another file is named"
(`src/Effect4/Program/Eff.lean:506-508`). Twenty-five of the twenty-eight rows carry such a line (`perform`,
`branch` and `select` cite our own documents instead). I resolved all twenty-five against the pinned tree:

- **Seven land on the declaration the row names.** `sync` → `:929`, `yieldNow` → `yieldNowWith` `:982`,
  `service` → `:2059`, `provideService` → `:2202`, `uninterruptible` → `:4302`, `interruptible` → `:4331`,
  `provideLayer` → `internal/layer.ts:8`.
- **Four land inside the named declaration but not at its head**, which is fine as a citation:
  `gen` `:1184` (declared `:1175`), `whileLoop` `:4628` (declared `:4624`), `catchIf` `:2798-2810` (declared
  `:2760`), `acquireRelease` `:3978` (declared `:3971`).
- **Fourteen do not resolve to the named declaration at all.** With the true line in the pin beside each:

  | row | our cite | what is actually at that line | the declaration in the pin |
  | --- | --- | --- | --- |
  | `succeed` | `:1275` | inside `export const fn` (`:1226`) | `:920` |
  | `fail` | `:1322` | blank, inside `fn` | `:926` |
  | `failCause` | `:1330` | blank, inside `fn` | `:923` |
  | `yieldError` | `:1226` | `export const fn` | no `yieldableError` export in `internal/effect.ts` |
  | `suspend` | `:1093` | inside `withFiberId` (`:1092`) | `:939` |
  | `bind` (`Effect.flatMap`) | `:1590` | inside `race`'s options type (`:1583`) | `:1663` |
  | `catchCause` | `:2417` | inside `replicateEffect` (`:2400`) | `:2475` |
  | `matchCause` (`matchCauseEffect`) | `:2645` | inside `tapCauseIf` (`:2624`) | `:3427` (`matchCause` `:3468`) |
  | `onExit` | `:4006` | inside `onExitPrimitive` (`:4002`) | `:4032` |
  | `exit` | `:2320` | inside `filterOrFail` (`:2315`) | `:3621` |
  | `callback` | `:1109-1143` | inside `callbackOptions` (`:1102`) | `:1163` |
  | `awaitFiber` | `:5291`, `:5304` | inside `forkDetach` (`:5287`) | `fiberAwait` `:767`, `fiberJoin` `:814` |
  | `withFiber` | `:1147` | inside `callbackOptions` | `internal/core.ts:556` (not in `internal/effect.ts` at all) |
  | `scoped` | `:3960` | inside `scopeUse` (`:3950`) | `:3938` |

By contrast **every one of the nineteen rows in `src/Effect4/Codegen/Forms.lean:90-123` cites a line that lands
on the declaration it names**: `void` `:1024`, `die` `:1018`, `yieldKey` `:2059`, the three `andThen` rows
`:1417`, `as` `:1386`, `asVoid` `:1467`, the two `tap` rows `:1442`, `ensuring` `:4043`, `matchCause` `:3468`,
`matchCauseEffect` `:3427`, `yieldNow` `:997`, `forkChild` `:5228`, `forkDetach` `:5287`, `forkIn` `:5337`,
`forkScoped` `:5382`, `releaseOne` `:3971`. So do the nine `Layer.ts` lines in the `LayerTerm` doc comments
(`:1074`, `:1427`, `:1512`, `:2258`, `:2704`, `:1850`, `:3850`, `:3327`, `:1652`, plus `:411`, `:438`, `:1438`
in the prose). So this is not a general rot; it is one table that was written early and never re-pinned. It is
exactly the "citation existence gate" candidate that the 2026-09-05 cleanup review ranked first, and it is now
a fourteen-row worked example for whoever builds that gate: a check that every `vendor/effect-4.0.0-rc.112/…:N`
in the tree resolves to a declaration whose name matches the row's `combinator` column would have caught all
fourteen. **Nothing in this note depends on those citations**; I resolved every rc.112 line I quote directly
against the pinned files.

## 9. Receipt

**Read in full (our side).** `docs/research/2026-09-16-select-and-iterate-ready-packet.md` §0, §1.1-§1.9, §3b,
§3c, §4, §5 (the §2 loop sections were read; §1.6-§1.7 skimmed for the ledger only).
`docs/research/2026-09-16-generation-medium-workshop.md` §1, §1b, §5, §5b. `src/Effect4/Program/Eff.lean`
(all 567 lines). `src/Effect4/Program/Authoring/Lifts.lean` (all 404 lines).
`src/Effect4/Program/Authoring/Sugar.lean` (all 42). `src/Effect4/Codegen/Forms.lean` (all 202).
`src/Effect4/Program/Native.lean` (all 371). `tools/Effect4Gen/binders.json` (all 51).
`src/Effect4/Program/Packages.lean` (all 53).

**Read in part (our side), for the specific facts cited.** `src/Effect4/Program/Decision.lean` (the
declarations and `arms_length`), `src/Effect4/Program/Ty.lean` (the `Ty` constructors, `result`/`exit`/`fiber`
abbrevs, `diffTag`/`taggedColumn`/`payloadOf`/`payloadTy`), `src/Effect4/Program/Typing.lean` (`EffTy`,
`joinAnswer`, `catchIfError`, the `select`/`exit`/`whileLoop` arms, `LayerTy` and `Requirement`),
`src/Effect4/Api.lean:255-360` (`replay`, `Tape.Complete`, `run`, `runSync`, `Run.trace`, `replayChecked`,
`replaySteps`), `src/Effect4/Machine/Supervision.lean` (`MaskMode`, `ForkOptions`, `cases_receipt`),
`src/Effect4/Machine/Wake.lean:119-165` (`WakeList`), `src/Effect4/Schema/Bridge.lean` (the two retractions,
`effDocument`, `rowDocument`), `src/Effect4/Api/TestClock.lean:38`, and greps for `raceAll` across
`src/Effect4/Laws/**` (`Clauses.lean:1615`, `Witnesses.lean:386`, `:438`).

**Read in full (pinned rc.112).** `Filter.ts` (1191 lines: header, every constructor and combinator).
`Pull.ts:1-90` (the model and the extractors; the rest of the module skimmed). `internal/matcher.ts:1-60`,
`:640-676`. `internal/schedule.ts` (all 248). `internal/executionPlan.ts:1-90`. `ExecutionPlan.ts:90-200`.
`Semaphore.ts:205-270`. `Latch.ts:161-240`. `Queue.ts:167-250`, `:335-360`, `:448-510`.
`unstable/workflow/Activity.ts:123-300`. `unstable/persistence/RateLimiter.ts:1-45`.

**Read closely by section (pinned rc.112).** `Effect.ts`: the full export list (220 names with their lines) and
the bodies of `all`, `partition`, `when`, `catchTag`, `catchTags`, `retry`/`Retry.Options`, `fn`, `Do`/`bindTo`,
`gen`. `internal/effect.ts`: `succeed`/`fail`/`failCause`/`sync`/`suspend`/`promise`/`callback`, `flatMap`/`map`/
`andThen`/`tap`/`as`/`asVoid`/`zip`/`zipWith`/`flatten`, the whole `catch*` family (`catchCause`, `catch_`,
`catchIf`, `catchFilter`, `catchTag`, `catchTags`, `catchCauseFilter`, `catchNoSuchElement`, `catchDefect`),
`option`/`result`/`exit`, `matchEager`, `when`, `timeout`/`timeoutOrElse`, `race`/`raceAll`/`raceFirst`/
`raceAllFirst`, `forEach`/`forEachSequential`/`whileLoop`/`all`/`partition`/`reduce`/`findFirstFilter`,
`acquireRelease`/`acquireUseRelease`/`addFinalizer`/`onExit`/`ensuring`/`onInterrupt`, `uninterruptible`/
`interruptible`/`uninterruptibleMask`/`interruptibleMask`, `cached`, `Do`/`bindTo`/`bind`, `makeSpan*`,
`gen`/`fnUntraced`, and every `dual` predicate I name. `Schedule.ts`: the model, `fromStep`,
`fromStepWithMetadata`, `metadataFn`, `recurs`, `spaced`, `exponential`, `fibonacci`, `jittered`, `passthrough`.
`Schema.ts`: the full export list (~400 names) plus `tag`, `tagDefaultOmit`, `TaggedStruct`, `toTaggedUnion`
(including `walk`, `match`, `matchOrElse`), `TaggedUnion`. `Match.ts`: the full export list plus `exhaustive`,
`tagsExhaustive`, `not`, `SafeRefinement`. `Tracer.ts:372-432`. `Metric.ts:111-123`. `Queue.ts`, `PubSub.ts`,
`Option.ts`, `Result.ts`, `Exit.ts`, `Cause.ts`, `Deferred.ts`, `Fiber.ts`, `Scope.ts`, `Context.ts`,
`Semaphore.ts`, `Latch.ts`, `Config.ts`: full export lists with line numbers, plus the specific declarations
cited. `Stream.ts:1-50`, `:122-127`. `Channel.ts:140-172`. `Config.ts:1-135`, `:252-290`.

**Export lists taken but bodies not read.** `PartitionedSemaphore.ts`, `Pool.ts`, `RcMap.ts`, `RcRef.ts`,
`FiberHandle.ts`, `FiberMap.ts`, `FiberSet.ts`, `Cache.ts`, `ScopedCache.ts`, `Request.ts`,
`RequestResolver.ts`, `Logger.ts`, `FileSystem.ts`, `Path.ts`, `Terminal.ts`, `Stdio.ts`,
`unstable/process/ChildProcess.ts`, `PlatformError.ts`, `unstable/cli/{Command,Flag,Argument,Prompt}.ts`,
`unstable/httpapi/{HttpApi,HttpApiEndpoint}.ts`, `unstable/http/HttpRouter.ts`,
`unstable/ai/{Tool,Toolkit,McpServer}.ts`, `unstable/rpc/{Rpc,RpcGroup}.ts`,
`unstable/workflow/{Workflow,DurableDeferred,DurableClock}.ts`,
`unstable/cluster/{Snowflake,MessageStorage,Singleton}.ts`,
`unstable/persistence/{PersistedQueue,Persistence,RateLimiter}.ts`.

**Skimmed only (module headers, or one grep).** `Sink.ts`, `Take.ts`, `ChannelSchema.ts`, `SchemaAST.ts`,
`SchemaGetter.ts`, `SchemaIssue.ts`, `SchemaParser.ts`, `SchemaRepresentation.ts`, `SchemaTransformation.ts`,
`Layer.ts` (only the lines our `LayerTerm` doc comments cite), `Runtime.ts`, `ManagedRuntime.ts`,
`unstable/cluster/Sharding.ts` (the lock/release region only), `unstable/observability/*`,
`unstable/workflow/WorkflowEngine.ts` (the service interface only).

**Not reached at all.** `Stream.ts` beyond its head and type (20442 lines, every combinator),
`Channel.ts` beyond its type (12352 lines), `Sink.ts`, `Chunk.ts`, `Graph.ts`, `Trie.ts`, `HashMap.ts`,
`HashSet.ts`, `HashRing.ts`, `Differ.ts`, `JsonPatch.ts`, `JsonPointer.ts`, `JsonSchema.ts`, `Optic.ts`,
`Newtype.ts`, `Brand.ts`, `Redacted.ts`, `DateTime.ts`, `Duration.ts`, `Cron.ts`, `Crypto.ts`, `Encoding.ts`,
`BigDecimal.ts`, `Random.ts`, `Scheduler.ts`, `LayerMap.ts`, `LayerRef.ts`, `Resource.ts`,
`SubscriptionRef.ts`, `SynchronizedRef.ts`, every `Tx*.ts` (the transactional family, 11 modules, which is a
real omission for the concurrency addendum, since `Effect.tx`/`Effect.txRetry` at `Effect.ts:24271`, `:24397`
are the STM-style facility and I did not read their semantics), `testing/`, `unstable/eventlog/*`,
`unstable/devtools/*`, `unstable/reactivity/*`, `unstable/workers/*`, `unstable/socket/*`,
`unstable/encoding/*`, `unstable/schema/*`, `unstable/cluster/*` apart from the four files named above, and
`unstable/sql/*` apart from confirming the module list.

**Evidence words.** Nothing in this note is *proved* or *tested*: no Lean was built, no lane was run, no
theorem was checked (the brief is read-only and forbids `lake`/`make`). Every rc.112 statement is **reproduced**
in the sense that I read the pinned bytes at the line I cite, and the fourteen stale `arms` citations of §8b are
**reproduced** the same way. Every claim about our side is either a **reproduced** reading of the file cited, or
where it says "would", "could" or "the proof the machine could give", **assumed**: a design claim about what
the existing machinery makes provable, not a proof that it does.
