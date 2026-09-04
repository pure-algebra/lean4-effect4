# Effect rc.112 internals: a proof map for the component registry

Date: 2026-09-04.
Scope: the mutable data structures and runtime of `effect@4.0.0-rc.112`, read as the
object of a Lean 4 characterization effort; what the existing Lean reification in
`lean4-effect4` already covers; and a ranked, pinned plan for what to characterize next.

Every claim about library code below carries a `path:line` citation against the pin
described in section 0. Claims that could not be confirmed in source are marked
**NOT VERIFIED** in place.

---

## 0. Provenance, pins, and the relationship between the four copies

### 0.1 The pin

The reading copy is `/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src`.
Its `package.json` declares `4.0.0-rc.112`. The stated Queue hash was re-computed and
agrees:

```
dc355d1a09662ae7b023c98ad47b7fe71051becaf9d461f244c37ad0a4d3dc35  src/Queue.ts
```

The repository already carries a pin manifest. `Effect4/StdLib/Rc112.lean:20-38` declares
nineteen `(module, path, sha256)` triples. Eleven of them were re-computed against the
reading copy and all eleven agree byte for byte, including
`Queue.ts` (`Effect4/StdLib/Rc112.lean:30`),
`PubSub.ts` = `ae675198…b728a38` (`:31`),
`Stream.ts` = `d78feda9…6f3739f` (`:32`),
`Sink.ts` = `ca74a0a1…cf5b0710` (`:33`),
`Channel.ts` = `e96aab89…275a3883` (`:34`),
`Scheduler.ts` = `e4c35925…c349680`, and
`internal/effect.ts` = `0e32b42f…8cc641f0`.
The manifest is therefore already the right anchor for a registry PINS column; it does not
need to be re-invented.

### 0.2 The four copies and their relationship

| Copy | Version | Relationship to the pin |
|---|---|---|
| `foldlab/library/effects/node_modules/effect/src` | 4.0.0-rc.112 | The pin itself. 136 stable modules plus `internal/` and `unstable/`. |
| `lean4-effect4/vendor/effect-4.0.0-rc.112/src` | 4.0.0-rc.112 | A **byte-exact 13-file subset** of the pin. All eleven files compared (`Scope.ts`, `Deferred.ts`, `Ref.ts`, `Layer.ts`, `Scheduler.ts`, `Cause.ts`, `Exit.ts`, `Context.ts`, `internal/effect.ts`, `internal/core.ts`, `internal/layer.ts`) hash identically. It does **not** contain `Queue.ts`, `PubSub.ts`, `Channel.ts`, `Stream.ts`, `Sink.ts`, `Semaphore.ts`, or `Latch.ts`. |
| `effect-smol` | monorepo, `package.json` says `4.0.0`; git head `b9da199`, 2025-09-21 | **Substantially behind the pin.** `Queue.ts` differs by 197 code lines (comments stripped), `PubSub.ts` by 249, `internal/effect.ts` by 3,531. It has **no `Semaphore.ts`, `Latch.ts`, or `PartitionedSemaphore.ts`** at all, whereas the pin has all three. Its value is its test tree (section 3.4), not its source. |
| `ssh pc`: `C:\Users\kokok\Dev\effect4-host\node_modules\effect` | claimed rc.112 | Not consulted. The mac copy was complete for every question asked here. |

Consequence for the registry: **the pin is the only citable source of truth**; `vendor/` is a
faithful but partial mirror that must be extended before any new component can be cited from
inside the repository; `effect-smol` is a stale sibling whose tests are candidate fixtures
requiring re-verification, never ground truth.

### 0.3 rc.111 to rc.112 line drift

The `effect-nats-verified` transliteration and the design note
`jetstream-workflow-model/research/2026-08-22-effect-nats-subscriber-model-design-note.md` §3
rest on twenty-six distinct `Queue.ts` line ranges taken at rc.111. Each of the load-bearing
ones was re-read at rc.112:

| rc.111 cite | Claimed content | rc.112 status |
|---|---|---|
| `Queue.ts:343-360` | the `Open`/`Closing`/`Done` state union | Holds. `State<A,E>` opens at `Queue.ts:343`. |
| `Queue.ts:458` | `make` defaults strategy to `"suspend"` | Holds exactly: `Queue.ts:458`. |
| `Queue.ts:500` | `bounded(n) = make({capacity: n})` | Holds: `Queue.ts:500`. |
| `Queue.ts:645-668` | `offer` | Holds; body now `645-669`. |
| `Queue.ts:649`, `:654-658`, `:659`, `:667` | non-Open early return, zero-capacity branch, suspend branch, append-and-schedule | All four hold verbatim. |
| `Queue.ts:872` | `fail = failCause(causeFail(e))` | Holds: `Queue.ts:872`. |
| `Queue.ts:1000-1015` | `failCauseUnsafe` | Holds exactly. |
| `Queue.ts:1191-1210` | `shutdown` | Holds exactly. |
| `Queue.ts:1297-1298` | `takeAll = takeBetween(self,1,+inf)` | Holds exactly. |
| `Queue.ts:1426-1433` | `takeBetween` | Holds exactly. |
| `Queue.ts:1607-1608`, `:1614-1620` | `takeUnsafe` Done check and zero-capacity path | Hold; `takeUnsafe` spans `1606-1623`. |
| `Queue.ts:1711`, `:1789` | `size`, `sizeUnsafe` | Hold exactly. |
| `Queue.ts:1950-1953` | the four exit constants | Hold exactly. |
| `Queue.ts:1955-1967` | `releaseTakers` | Holds; declaration at `1955`, body to `1968`. |
| `Queue.ts:1969-1975` | `scheduleReleaseTaker` | Holds; declaration at `1969`, body to `1976`. |
| `Queue.ts:1994-1998` | the `takeN` path of `takeBetweenUnsafe` | Holds exactly. |
| `Queue.ts:2002-2015` | `offerRemainingSingle` | Holds; body to `2016`. |
| `Queue.ts:2038-2069` | `releaseCapacity` | Declaration moved to `2037`; body `2037-2070`. |
| `Queue.ts:2100-2114` | `finalize` | Holds exactly (file is 2,114 lines). |

**`Queue.ts` is line-stable across rc.111 and rc.112.** Every proved law in
`effect-nats-verified` that rests on a `Queue.ts` cite still points at the same code.

`internal/effect.ts` did drift. The rc.111 cites in the same design note land two to four
lines early at rc.112:

| rc.111 cite | rc.112 location |
|---|---|
| `internal/effect.ts:3811` (finalizers run last to first) | `internal/effect.ts:3815` |
| `internal/effect.ts:3813-3814` (sequential by default) | `internal/effect.ts:3817-3818` |
| `internal/effect.ts:3843-3852` (`scopeAddFinalizerExit`) | `internal/effect.ts:3845-3856` |
| `internal/effect.ts:3863-3873` (finalizer-map insertion) | `internal/effect.ts:3867-3890` |
| `internal/effect.ts:4645-4653` (`forEach` concurrency default) | `internal/effect.ts:4648-…` |

`Deferred.ts` drifted heavily: `doneUnsafe`, cited at `:856-869` in the fiber-machine brief,
is at `Deferred.ts:1648-1662` at rc.112. Any registry that reuses those brief cites must
re-pin them.

---

## 1. Data-structure inventory

The columns are: the concrete mutable state; the state-changing verbs, internal ones first
because they are where the semantics live; the atomicity boundary; the nondeterminism; and
the invariants the code visibly relies on.

### 1.1 `Queue`

**State.** Four mutable fields on the queue object plus a three-case tagged union
(`Queue.ts:167-176` for `Enqueue`, `:303-306` for `Queue`, `:343-372` for `State`):

| Field | Type | Cite |
|---|---|---|
| `capacity` | `number`, `+Infinity` when unbounded | `Queue.ts:169`, default `Queue.ts:457` |
| `strategy` | `"suspend" \| "dropping" \| "sliding"`, immutable after construction | `Queue.ts:169`, default `Queue.ts:458` |
| `dispatcher` | `SchedulerDispatcher`, **captured from the creating fiber and never re-read** | `Queue.ts:455` |
| `messages` | `MutableList<A>`, a bucketed FIFO | `Queue.ts:172`, `:459` |
| `scheduleRunning` | `boolean` reentrancy guard | `Queue.ts:174`, `:460` |
| `state` | `Open{takers,offers,awaiters}` \| `Closing{…,exit}` \| `Done{exit}` | `Queue.ts:343-372` |

`takers` and `awaiters` are `Set` of resume callbacks; `offers` is a `Set` of `OfferEntry`,
each either `Single{message,resume}` or `Array{remaining,offset,resume}` (`Queue.ts:374-386`).
`MutableList` is a linked list of array buckets with a per-bucket `offset` and a cached
`length` (`MutableList.ts:35-38`, `:155-158`, `:189-197`).

**Verbs.** Nine internal helpers carry the whole semantics:

| Verb | Span | What it does |
|---|---|---|
| `releaseTakers` | `Queue.ts:1955-1968` | Clears `scheduleRunning`; drains `takers` one at a time, **breaking as soon as `messages.length` hits zero**. |
| `scheduleReleaseTaker` | `Queue.ts:1969-1976` | Enqueues `releaseTakers` on the queue's own dispatcher at priority 0, guarded by `scheduleRunning`. |
| `takeBetweenUnsafe` | `Queue.ts:1977-2001` | The only take decision procedure. Handles `Done`, degenerate bounds, the zero-capacity rendezvous, and the `takeN` path. |
| `offerRemainingSingle` | `Queue.ts:2002-2016` | Parks one offerer as a `Single` entry, with an interruption cleanup that removes it. |
| `offerRemainingArray` | `Queue.ts:2017-2036` | The batch analogue. |
| `releaseCapacity` | `Queue.ts:2037-2070` | Admits parked offers into `messages` up to `capacity`, resuming each; finalizes a `Closing` queue once both `messages` and `offers` are empty. |
| `awaitTake` | `Queue.ts:2071-2083` | Parks one taker, with removal-on-interrupt. |
| `takeAllUnsafe` | `Queue.ts:2084-2099` | Drains everything, with the same zero-capacity trick. |
| `finalize` | `Queue.ts:2100-2114` | The single `→ Done` transition; resumes **takers and awaiters, never offers**. |

The public surface (`offer` `:645-669`, `offerUnsafe` `:708-726`, `offerAll` `:762-774`,
`offerAllUnsafe` `:812-844`, `fail` `:872`, `failCause`, `failCauseUnsafe` `:1000-1015`,
`end` `:1058`, `interrupt` `:1153-1154`, `shutdown` `:1191-1210`, `clear` `:1248-1259`,
`takeAll` `:1297-1298`, `takeN`, `takeBetween` `:1426-1433`, `take` `:1474-1477`,
`poll` `:1513-1523`, `peek` `:1552-1561`, `takeUnsafe` `:1606-1623`, `await` `:1625-1666`,
`size` `:1711`, `isFull` `:1739`, `sizeUnsafe` `:1789`, `isFullUnsafe` `:1822`,
`into` `:1858-1948`) is sugar over those nine, exactly as the owner's hypothesis predicts.
`takeAll` is literally `takeBetween(self, 1, +Infinity)` (`Queue.ts:1297-1298`);
`end` is literally `failCause(self, causeFail(Done()))` (`Queue.ts:1058`);
`interrupt` is `failCause` with an interrupt cause (`Queue.ts:1153-1154`).

**Atomicity boundaries.** Three distinct ones, and the distinction is observable:

1. One synchronous JS function. `offerUnsafe`, `offerAllUnsafe`, `failCauseUnsafe`,
   `takeUnsafe`, `sizeUnsafe`, `shutdown`'s body, and every internal helper run to
   completion with no interleaving.
2. One Effect step. `offer`, `take`, `takeBetween`, `clear`, `poll`, `peek` are
   `internalEffect.suspend(…)` wrappers (`Queue.ts:646`, `:1475`, `:1427`, `:1249`,
   `:1514`, `:1553`); the fiber can be preempted between the wrapper and its retry.
   `take` is explicitly recursive: `takeUnsafe(self) ?? andThen(awaitTake(self), take(self))`
   (`Queue.ts:1474-1477`). A woken taker therefore **re-races** for the message and may find
   it gone.
3. A scheduled task. `scheduleReleaseTaker` (`Queue.ts:1974`) posts `releaseTakers` to a
   dispatcher; the wake-up is not inline with the offer.

**Nondeterminism.**

- Taker wake-up is a scheduled task on `self.dispatcher`, captured at construction from the
  *creating* fiber (`Queue.ts:455`, `internal/effect.ts:553-555`). A queue offered to by a
  fiber with a different dispatcher schedules its wake-up on the **creator's** queue, not the
  offerer's. Cross-dispatcher drain order is the second of the three named gaps in the Lean
  Deep machine, and `Effect4/Deep/Fibers.lean:1130` already records the synchronous-flush
  order as an assumption rather than a theorem.
- `Set` iteration order in `releaseTakers` (`Queue.ts:1960`) and `releaseCapacity`
  (`Queue.ts:2047`) is JS insertion order, which is deterministic per realm but is a fact
  about the host, not about the algorithm.
- The `take` retry loop means the identity of the taker that gets a given message depends on
  the dispatcher's drain order.

**Invariants the code visibly relies on.**

- **I-Q1.** `Closing ⟹ (messages.length > 0 ∨ offers.size > 0)`. `failCauseUnsafe` finalizes
  immediately when both are empty (`Queue.ts:1007-1011`), and `releaseCapacity` finalizes as
  soon as a `Closing` queue's buffer drains with no offers left (`Queue.ts:2040-2044`). An
  empty `Closing` queue is therefore unreachable, which is what makes the parked taker on a
  `Closing` queue safe from starvation.
- **I-Q2.** `Done` is absorbing. Every mutating verb tests `state._tag` first
  (`Queue.ts:647`, `:709`, `:813`, `:1001`, `:1192`, `:1607`, `:1956`, `:1981`, `:2038`,
  `:2101`).
- **I-Q3.** `sizeUnsafe` reports **buffered messages only**, never parked offers
  (`Queue.ts:1789`), and reports `0` for `Done`. Documented at `Queue.ts:1682-1707`.
- **I-Q4.** The failure exit is always `zipRight(exitFailCause(cause), exitFailDone)`
  (`Queue.ts:1005-1006`), so every terminal cause carries `Done` behind the user's cause.
- **I-Q5.** `finalize` never resumes `offers`. Only `shutdown` does, explicitly, after
  `finalize` returns (`Queue.ts:1198-1207`). A queue completed by `fail`/`end`/`interrupt`
  with parked offerers relies on `releaseCapacity` to drain them, which is precisely why I-Q1
  matters.
- **I-Q6.** `capacity` is temporarily mutated to 1 and back to 0 in the rendezvous paths
  (`Queue.ts:1985-1990`, `:1614-1620`, `:2091-2096`). This is a re-entrancy hazard the code
  tolerates because the intervening `releaseCapacity` call cannot yield.

**Strategies.** `"suspend"`, `"dropping"`, `"sliding"` are a *field*, branched on inside
`offer` (`Queue.ts:648-664`) and `offerUnsafe` (`Queue.ts:711-721`); `offerAllUnsafe` treats
`sliding` and unbounded together (`Queue.ts:815-826`). They are not separate objects and
should be parameters, not components (section 4.6).

### 1.2 `PubSub`

**State.** A composite, unlike `Queue` (`PubSub.ts:64-74`): a backing `Atomic<A>` ring, a
`Subscribers` map, its own `Scope.Closeable`, a `Latch` shutdown hook, a
`MutableRef<boolean>` shutdown flag, and a `Strategy<A>`.

`Subscribers` is `Map<BackingSubscription<A>, Set<MutableList<Deferred<A>>>>`
(`PubSub.ts:111-114`). Each `Subscription` carries its own `pollers: MutableList<Deferred<A>>`
and a `ReplayWindow` (`PubSub.ts:236-247`).

Four backing implementations: `BoundedPubSubArb` (`PubSub.ts:1859-1957`), `BoundedPubSubPow2`
(`:2053-2154`), `BoundedPubSubSingle` (`:2248-2330`), `UnboundedPubSub` (`:2405-…`). The
arbitrary-capacity one is a ring of `capacity` slots with a monotone `publisherIndex`, a
`subscribersIndex`, and a per-slot **outstanding-subscriber count** `subscribers[i]`
(`PubSub.ts:1860-1865`).

**Verbs.** Atomic: `publish`, `publishAll`, `slide`, `subscribe`, `size`, `isEmpty`,
`isFull`, `replayWindow` (`PubSub.ts:86-97`). BackingSubscription: `poll`, `pollUpTo`,
`size`, `isEmpty`, `unsubscribe` (`PubSub.ts:100-107`). Strategy: `handleSurplus`,
`onPubSubEmptySpaceUnsafe`, `completePollersUnsafe`, `completeSubscribersUnsafe`, `shutdown`
(`PubSub.ts:155-197`). Public: `publish` `:907-1011`, `publishUnsafe` `:1047-1125`,
`publishAll` `:1162-1251`, `subscribe` `:1304-1315`, `take` `:1371-1389`, `takeAll`
`:1419-1437`, `takeUpTo` `:1497-1583`, `takeBetween` `:1616-1685`, `shutdown` `:757-765`,
`awaitShutdown` `:863`, `remaining` `:1766`, plus the private `unsubscribe` `:1317-1350` and
`pollForItem` `:1439-1461`.

**Atomicity.** `publishUnsafe` is one synchronous function (`PubSub.ts:1065-1073`).
`publish` is a `suspend` wrapper that may fall through to `handleSurplus`, which parks the
publisher on a `Deferred` (`PubSub.ts:2729-2746`). `take` is a `suspend` wrapper that either
polls or parks on a `Deferred` registered in `pollers` (`PubSub.ts:1371-1389`, `:1439-1461`).

**Nondeterminism.** `Map` and `Set` iteration order over `subscribers`; the order in which
parked publishers are re-admitted by `onPubSubEmptySpaceUnsafe` (`PubSub.ts:2749-2769`), which
re-`prepend`s an unpublishable entry and loops; `Deferred` completion ordering.

**Invariants and one grade-relevant surprise.**

- **I-P1.** With **zero subscribers, `publish` returns `true` and discards the value**. The
  ring branch is guarded by `if (this.subscriberCount !== 0)` (`PubSub.ts:1897-1905`), and
  `publishAll` returns `[]` early in the same case (`PubSub.ts:1912-1918`). Only the replay
  buffer sees it. Any `noLoss` grade for `PubSub` must be stated relative to *subscribers
  present at publish time*, never to future subscribers.
- **I-P2.** `slide` decrements the slot's outstanding count to `0` and writes an
  `AbsentValue` sentinel (`PubSub.ts:1944-1953`), so a slot is never read after sliding.
- **I-P3.** `subscribe` is `uninterruptible` and forks a child of the PubSub's own scope, then
  registers `Scope.close` on the *caller's* scope (`PubSub.ts:1304-1315`). Unsubscription is
  therefore scope-driven, and `unsubscribe` is itself `uninterruptible` (`PubSub.ts:1317-1350`).
- **I-P4.** `take` prefers the replay window over the ring (`PubSub.ts:1376-1379`), and skips
  polling entirely when `pollers` is non-empty (`PubSub.ts:1380-1382`), which is the FIFO
  discipline among takers that `Queue` does not have.

### 1.3 `Stream` / `Channel` / `Sink`: the pull protocol

This layer has **no mutable state of its own**. It is a function algebra over `Effect`,
`Scope`, and the concurrency primitives.

- `Pull<A,E,Done,R> = Effect<A, E | Cause.Done<Done>, R>` (`Pull.ts:40-42`). One element per
  evaluation; completion is carried in the error channel as `Cause.Done`.
- A `Channel` is a `transform: (upstream: Pull, scope: Scope) => Effect<Pull>`
  (`Channel.ts:283-287`, projected by `toTransform` at `Channel.ts:436-441`).
- `Stream<A,E,R>` stores exactly one field, `channel: Channel<NonEmptyReadonlyArray<A>, E, void, …>`
  (`Stream.ts:122-127`).
- `Sink<A,In,L,E,R>` stores exactly one field,
  `transform: (upstream: Pull<NonEmptyReadonlyArray<In>, never, void>, scope) => Effect<End<A,L>, E, R>`
  (`Sink.ts:63-73`).

State appears only where a combinator allocates a `Queue`, a `Latch`, a `Semaphore`, a
`PubSub`, or a fiber. The complete set of `Queue` allocation sites in the stable tree is:

| Site | Owner | Capacity |
|---|---|---|
| `Channel.ts:467-468` | `asyncQueue` | `options.bufferSize` |
| `Channel.ts:2361` | `mapEffectConcurrent` | **0** (rendezvous) |
| `Channel.ts:2392-2396` | `mapEffectConcurrent` | `concurrencyN - 2` |
| `Channel.ts:8128` | `mergeAll` | see source |
| `Channel.ts:8438` | `merge` | see source |
| `Channel.ts:9297` | `buffer` | caller-supplied |
| `Channel.ts:9467` | `bufferArray` | caller-supplied |
| `Channel.ts:11723` | `toQueue` | caller-supplied |
| `Channel.ts:11867` | `toQueueArray` | caller-supplied |
| `Stream.ts:1417` | `fromEventListener` (via `offerUnsafe`) | caller-supplied |
| `Stream.ts:6474-6475`, `:6542` | `partitionQueue` | `capacity ?? DefaultChunkSize` |
| `Stream.ts:7010` | `partition` | `bufferSize ?? 16` |
| `Stream.ts:14274`, `:14281` | `groupByImpl` | unbounded out; `bufferSize ?? 4096` per key |
| `Stream.ts:14745` | `aggregateWithin` | caller-supplied |
| `Sink.ts:519` | `fromQueue` (via `offerAll`) | external |
| `Pool.ts:943`, `:975` | `strategyCreationTTL`, `strategyUsageTTL` | unbounded |
| `unstable/…` (18 modules import `Queue.ts`) | rpc, cluster, socket, sql, eventlog, ai, cli, devtools, reactivity, workers, persistence | out of scope here |

`Channel.ts:2361` is the load-bearing one for the registry: a **capacity-0** queue, which
exercises the rendezvous paths at `Queue.ts:654-658`, `:1614-1620`, `:1985-1990`, `:2091-2096`
that the `effect-nats-verified` model explicitly declares out of scope. Any grade for
concurrent `mapEffect` composes through those paths.

### 1.4 `Scope`

**State.** Three cases, and the `Open` case is space-optimized
(`Scope.ts:45-48`, `:99-190`):

```
Empty                                          -- no finalizer yet
Open { finalizerKey?, finalizer?, finalizers? } -- one inline, or a Map
Closed { exit }
```

plus an immutable `strategy: "sequential" | "parallel"` (`Scope.ts:47`).

**Verbs.** `scopeMakeUnsafe` (`internal/effect.ts:3915-3921`),
`scopeAddFinalizerUnsafe` (`:3867-3890`), `scopeRemoveFinalizerUnsafe` (`:3891-3906`),
`scopeCloseUnsafe` (`:3779-3799`), `scopeCloseFinalizers` (`:3806-3829`),
`scopeForkUnsafe` (`:3834-3846`), `scopeFinalizerCountUnsafe` (`:3908-3913`).

**Ordering.** Finalizers run in **reverse insertion order**:
`for (let i = arr.length - 1; i >= 0; i--)` (`internal/effect.ts:3815`). Sequential strategy
awaits each via `exit(...)`; parallel forks each as an immediate, daemon, interrupt-inheriting
child (`internal/effect.ts:3817-3821`) and then `fiberAwaitAll`s them (`:3822-3824`). Order
depends on `Map` insertion order, which JS guarantees.

**A first-class asymmetry.** `scopeCloseUnsafe` has three fast paths before it ever reaches
`scopeCloseFinalizers`: `Empty` returns immediately (`:3782-3785`), the inline single
finalizer is **returned directly** (`:3788-3790`), and a one-entry map is likewise returned
directly (`:3794-3796`). Only two or more finalizers go through `scopeCloseFinalizers` and its
`exitAsVoidAll` aggregation (`:3826`). Therefore **a failing lone finalizer propagates its own
cause, while a failing finalizer among several is aggregated**. This is an observable
difference in error shape driven purely by finalizer count, and it is exactly the kind of
defensive branch a Lean model must reproduce rather than normalize away.

**Invariants.**

- **I-S1.** `Closed` is absorbing; `scopeAddFinalizerUnsafe` silently does nothing on a
  `Closed` scope (`internal/effect.ts:3867-3889` has no `Closed` branch), while the effectful
  `scopeAddFinalizerExit` runs the finalizer immediately instead (`:3852-3854`).
- **I-S2.** The `Open` representation is a disjunction the code maintains by hand: exactly one
  of `finalizer` and `finalizers` is defined at a time, and the promotion from the inline slot
  to the map preserves the inline entry first (`internal/effect.ts:3874-3878`).
- **I-S3.** `scopeForkUnsafe` installs a **mutually cancelling finalizer pair**: the parent
  gets a finalizer closing the child, and the child gets a finalizer removing that entry from
  the parent, both under the same fresh key (`internal/effect.ts:3840-3842`). This is the
  cycle-avoidance discipline a Lean model must reproduce or it will leak entries.
- **I-S4.** `scopeMakeUnsafe` shares one `constScopeEmpty` object across every scope
  (`internal/effect.ts:3920`, `:3923`). Safe only because the `Empty → Open` transition
  *replaces* `state` rather than mutating it (`:3869`).

### 1.5 `Fiber`, the run loop, the stack, and interruption

**State.** `FiberImpl` (`internal/effect.ts:505-733`) has thirteen own mutable fields plus a
cached-context block:

| Field | Cite |
|---|---|
| `id` (from a module-global counter) | `:511`, `:527` |
| `interruptible: boolean` | `:514`, `:529` |
| `currentOpCount: number` | `:513`, `:530` |
| `_stack: Array<Primitive>` | `:515`, `:531` |
| `_observers: Array<(exit) => void>` | `:516`, `:532` |
| `_exit: Exit \| undefined` | `:517`, `:533` |
| `_children: Set<FiberImpl> \| undefined` | `:518`, `:534` |
| `_interruptedCause: Cause<never> \| undefined` | `:519`, `:535` |
| `_yielded: Exit \| (() => void) \| undefined` | `:520`, `:536` |
| `_running: boolean` | `:521`, `:537` |
| `_deferredInterrupt: boolean` | `:522`, `:538` |
| `context` and the eight derived caches | `:540-551`, written by `setContext` `:709-730` |
| `_dispatcher`, lazily made | `:552-555` |

**The seventeen primitives.** The set is closed at rc.112 and each op tag was located exactly:

| Op | Cite | Op | Cite |
|---|---|---|---|
| `Success` | `internal/core.ts:510` | `Iterator` | `internal/effect.ts:1360` |
| `Failure` | `internal/core.ts:530` | `OnSuccess` | `internal/effect.ts:1684` |
| `WithFiber` | `internal/core.ts:559` | `OnFailure` | `internal/effect.ts:2496` |
| `YieldableError` | `internal/core.ts:572` | `OnSuccessAndFailure` | `internal/effect.ts:3460` |
| `Sync` | `internal/effect.ts:930` | `Exit` | `internal/effect.ts:3626` |
| `Suspend` | `internal/effect.ts:942` | `OnExit` | `internal/effect.ts:4007` |
| `Yield` | `internal/effect.ts:983` | `SetInterruptible` | `internal/effect.ts:4313` |
| `Async` | `internal/effect.ts:1110` | `While` | `internal/effect.ts:4629` |
| `AsyncFinalizer` | `internal/effect.ts:1148` | | |

There are exactly fourteen `_stack.push` sites: `internal/effect.ts:1134`, `:1152`, `:1368`,
`:1686`, `:2498`, `:3462`, `:3628`, `:4010`, `:4015`, `:4308`, `:4326`, `:4350`, `:4633`,
`:4640`. `_stack` is popped only in `getCont` (`:689`) and cleared on completion (`:625`).

**Atomicity.** The run loop is a `while (true)` trampoline (`internal/effect.ts:638-668`)
that runs to a `Yield` sentinel or to an `Exit`. Between two iterations there is no
interleaving; `_deferredInterrupt` is the mechanism by which an interrupt arriving *during*
the loop is deferred to the next iteration (`:639-642`). The op-budget check rewrites the
current effect to `flatMap(yieldNow, () => prev)` on the first positive
`shouldYield` (`:645-652`), where `shouldYield` is
`currentOpCount >= maxOpsBeforeYield` (`Scheduler.ts:174-176`) with default `2048`
(`Scheduler.ts:269-272`).

**Interruption.** `interruptUnsafe` (`internal/effect.ts:574-594`) is a no-op after `_exit`,
combines a fresh `Interrupt` cause into `_interruptedCause`, and then branches on
`interruptible` and `_running`: running gives `_deferredInterrupt = true`, suspended gives an
immediate `evaluate(failCause(...))`, uninterruptible records only. `SetInterruptible.contAll`
re-fires the recorded cause the moment interruptibility is restored
(`internal/effect.ts:4314-4319`). `uninterruptible`, `uninterruptibleMask`, `interruptible`,
`interruptibleMask` all work by mutating `fiber.interruptible` and pushing the inverse marker
(`:4302-4311`, `:4331-4339`, `:4340-4354`, `:4355-4366`).

Interruption **crossing a component boundary** is always mediated by the `Async` primitive's
cleanup effect. `callbackOptions` (`internal/effect.ts:1102-1143`) pushes an `asyncFinalizer`
carrying the registration's returned cancel effect, and `asyncFinalizer[contE]` runs it only
when the cause `hasInterrupts` (`:1156-1159`). Every parking verb in the library returns such
a cleanup: `Queue.awaitTake` removes the taker (`Queue.ts:2077-2082`),
`Queue.offerRemainingSingle` removes the offer entry (`Queue.ts:2010-2015`),
`Deferred._await` splices the resume out (`Deferred.ts:178-186`),
`Semaphore.waitForPermits` deletes the observer (`Semaphore.ts:218-221`),
`Latch.await` searches both `waiters` and `scheduled` (`internal/effect.ts:5624-5637`).
`PubSub` instead uses `Effect.onInterrupt` around a `Deferred.await`
(`PubSub.ts:1452-1458`).

**Fork.** `forkUnsafe` (`internal/effect.ts:5264-5286`) creates the child with the parent's
context **by reference** (`:5273`), starts it either immediately or as a scheduled task
(`:5275-5278`), and, for non-daemon children, registers it in `parent.children()` with a
self-removing observer (`:5279-5283`). Child interruption on parent exit is a tree-shakeable
middleware installed by `interruptChildrenPatch` (`:6656-6658`) and consulted in `evaluate`
(`:611-616`).

**Run entry points.** `runForkWith` `:5413-5440`; `fiberRunIn` `:5441-5463`;
`runSyncExitWith` `:5536-5547`. The last is the determinism lever: it constructs a
`MixedScheduler("sync")` and calls `fiber._dispatcher?.flush()` (`:5541-5543`).

### 1.6 `Scheduler` and the dispatcher

**State.** `PriorityBuckets` holds `buckets: Array<[priority, tasks]>` kept sorted ascending
by priority with FIFO within a bucket (`Scheduler.ts:105-131`). A
`MixedSchedulerDispatcher` owns one `PriorityBuckets`, a `running` slot, and a
`setImmediate` function (`Scheduler.ts:193-202`).

**Verbs.** `scheduleTask` (`Scheduler.ts:207-212`), `afterScheduled` (`:217-220`),
`runTasks` (`:225-233`), `flush` (`:238-246`), `drain` (`:126-130`),
`Scheduler.shouldYield` (`:174-176`), `Scheduler.makeDispatcher` (`:188-190`).

**One subtlety worth a theorem.** `this.running` holds the **cancel closure** returned by
`setImmediate`, not the task (`Scheduler.ts:210`, and both `setImmediate` shims return a
canceller at `Scheduler.ts:84-93` and `:95-103`). `flush` therefore calls `this.running()` to
*cancel* the pending host callback before draining synchronously (`Scheduler.ts:239-245`).
This is what makes `runSync` deterministic and is the hinge on which any replay harness turns.

**Execution modes.** `"async"` uses `globalThis.setImmediate` or `setTimeout(f, 0)`;
`"sync"` uses a cancellable `Promise.resolve().then` microtask (`Scheduler.ts:156-162`).

**The complete task alphabet.** There are exactly **seven** `scheduleTask` call sites in the
stable tree, and this is a closed, checkable list:

| # | Site | Task |
|---|---|---|
| 1 | `internal/effect.ts:986` | yield resume |
| 2 | `internal/effect.ts:5277` | deferred child start |
| 3 | `internal/effect.ts:5583` | `Latch.flushScheduled` |
| 4 | `Queue.ts:1974` | `releaseTakers` |
| 5 | `Semaphore.ts:260` | permit-observer sweep |
| 6 | `Pool.ts:703` | `wakeWaiters` |
| 7 | `Effect.ts:24350` | STM `commitTransaction` pending wake |

Site 4 is the only one that posts to a **stored** dispatcher (`self.dispatcher`,
`Queue.ts:1974`) rather than the acting fiber's. All others read
`fiber.currentDispatcher`.

### 1.7 `Semaphore`

**State.** `waiters: Set<() => void>`, `taken: number`, `permits: number`
(`Semaphore.ts:226-228`); `free` is derived (`Semaphore.ts:234-236`).

**Verbs.** `waitForPermits` (`Semaphore.ts:207-224`), `take` (`:238-247`),
`takeIfAvailable` (`:249-255`), `releaseUnsafe` (`:257-267`), `resize` (`:270-277`),
`release` (`:279-281`), `releaseAll` (`:283-285`), `withPermits` (`:287-307`),
`withPermit` (`:309`), `withPermitsIfAvailable` (`:311-320`).

**Atomicity.** `taken += n` happens inside a `suspend` (`Semaphore.ts:239-246`), so acquisition
is one Effect step. Release is one synchronous function that then **schedules** the observer
sweep (`Semaphore.ts:258-266`).

**Documented non-fairness.** The doc comment on `take` states that a smaller later request may
overtake a larger earlier one (`Semaphore.ts:123-133`), and the implementation confirms it:
`waitForPermits`'s observer returns early when `self.free < n` (`Semaphore.ts:212`) and the
sweep breaks on `free <= 0` (`Semaphore.ts:262`), so a large waiter is skipped while a small
one behind it succeeds. **There is no FIFO guarantee**, and the registry should record this as
a disproved property rather than an unproved one.

**Invariant hazard.** `resize` sets `permits` unconditionally and only guards the release path
(`Semaphore.ts:270-277`), so `free` can be **negative** after a shrink. `takeIfAvailable`
and `withPermitsIfAvailable` compare `free < n` (`:251`, `:313`), which behaves correctly for
negative `free`, but any Lean model using `Nat` will be wrong. `free : Int`.

### 1.8 `Latch`

**State.** `waiters: Array<resume>`, `scheduled: Array<resume> | undefined`,
`_isOpen: boolean` (`internal/effect.ts:5569-5571`).

**Verbs.** The class spans `internal/effect.ts:5568-5651`, with the constructors
`makeLatchUnsafe` at `:5654` and `makeLatch` at `:5657`. Members: `scheduleUnsafe`
(`:5577-5591`), `flushScheduled` (`:5592-5599`), `flushWaiters` (`:5600-5610`),
`open` (`:5612-5616`), `release` (`:5617`), `openUnsafe` (`:5618-5623`),
`await` (`:5624-5640`), `closeUnsafe` (`:5641-5645`), `close` (`:5646`),
`whenOpen` (`:5647`), `isOpen` (`:5648-5650`).

**The atomicity contrast worth isolating.** `open` (the Effect) defers waiter release to a
scheduled task (`internal/effect.ts:5583`); `openUnsafe` flushes **synchronously**
(`:5621`). The two differ observably in interleaving, and the code carries two explanatory
comments about exactly this: `flushWaiters` swaps both arrays out before any resume runs
because a resumed waiter can reentrantly close the latch and register new waiters
(`:5601-5603`), and `Deferred.doneUnsafe` clears `resumes` before resuming for the mirror
reason (`Deferred.ts:1651-1654`). These comments are the strongest available evidence of the
re-entrancy invariants the authors rely on.

### 1.9 `Deferred`

**State.** Two optional fields: `effect?: Effect<A,E>` and
`resumes?: Array<(effect) => void>` (`Deferred.ts:58-61`, initialized `:140-145`).

**Verbs.** `makeUnsafe` (`:140-145`), `_await` (`:173-186`), `doneUnsafe` (`:1648-1662`),
`isDoneUnsafe` (`:1382`), plus the family `complete`, `completeWith`, `done`, `fail`,
`failSync`, `failCause`, `failCauseSync`, `die`, `dieSync`, `succeed`, `sync`, `interrupt`
(`:1231-1232`), `interruptWith`, `into`, `poll`.

**Atomicity.** `doneUnsafe` is one synchronous function; it is the only empty-to-complete
transition and it resumes every waiter **inline** (`Deferred.ts:1651-1660`). There is no
scheduled task.

**Invariant.** Completion is single-shot: `if (self.effect) return false` (`:1649`), and
`isDoneUnsafe` is exactly `self.effect !== undefined` (`:1382`).

### 1.10 `Ref` and its derivatives

`Ref` is a one-field box; every operation is `Effect.sync` over `self.ref.current`
(`Ref.ts:142-146`, `:200`, `:401-403`). It is atomic within one synchronous function and has
no invariants beyond well-typedness.

The derivatives are pure compositions, which is the useful fact:

| Type | Composition | Cite |
|---|---|---|
| `SynchronizedRef` | `Ref` + `Semaphore(1)` | `SynchronizedRef.ts:37-40`, `:67` |
| `SubscriptionRef` | `Ref` + `Semaphore(1)` + `PubSub` with `replay: 1` | `SubscriptionRef.ts:37-40`, `:112-117` |

`SubscriptionRef.changes` is `Stream.fromPubSub(self.pubsub)` (`SubscriptionRef.ts:160`).
Their grades therefore *follow* from `Semaphore` and `PubSub` and need no independent model.

### 1.11 `Layer` memo map

**State.** `MemoMapImpl` holds `parent: MemoMap | undefined` and
`map: Map<Layer, MemoEntry>` (`Layer.ts:421-432`); each entry is
`{ observers: number, effect: Effect<Context>, finalizer }` (`Layer.ts:235-239`).

**Verbs.** `get` (`Layer.ts:434-444`), `getOrElseMemoize` (`:446-458`),
`memoMapBuild` (`:390-420`), `memoMapReuse` (`:241-252`).

**Mechanism.** `memoMapBuild` allocates a fresh child `Scope` and a `Deferred`, seeds the
entry with `observers: 1` and `effect: Deferred.await(deferred)`, registers a decrementing
finalizer on the requesting scope, builds into the layer scope, and on exit **replaces
`entry.effect` with the exit itself** and completes the deferred
(`Layer.ts:391-419`). Reuse increments `observers` and registers the same finalizer on the new
scope (`Layer.ts:241-252`). The layer scope closes exactly when `observers` reaches zero, at
which point the entry is deleted from the map (`Layer.ts:400-407`).

**Invariant.** `observers` counts live scope registrations; the entry is present in `map`
if and only if `observers > 0`. This is the reference-counting law a Lean model must prove,
and it is structurally identical to `RcMap`'s `refCount` (`RcMap.ts:163`, `:547`, `:728`,
`:738-739`, `:762`, `:968`).

### 1.12 `Context`

`Context` is an immutable `ReadonlyMap<string, unknown>` (`Context.ts:730`). The mutable part
lives on the fiber: `setContext` recomputes eight derived caches whenever the new context
does not share the old one's cache (`internal/effect.ts:709-730`), and resets `_dispatcher`
when the scheduler reference changes (`:716-719`). `Reference` adds a memoized
`defaultValue` under the key `~effect/Context/defaultValue` (`Context.ts:1582-1588`) and an
opt-in `fiberCached` flag (`Context.ts:2007`). Because context is fiber state rather than a
primitive, there is no `Provide` op in the seventeen.

---

## 2. What is already reified in `lean4-effect4`

### 2.1 The census and its coverage

`generated/effect-runtime-census.tsv` has the schema
`mechanism | kind | id | file | lines | span-sha256 | summary` (line 17) and **137 mechanism
rows** (the "97 rows" figure in circulation is stale). It declares twelve input files, all
under `vendor/effect-4.0.0-rc.112/src`, all byte-identical to the pin:
`internal/effect.ts`, `internal/core.ts`, `Scheduler.ts`, `Scope.ts`, `Exit.ts`, `Cause.ts`,
`Array.ts`, `Ref.ts`, `MutableRef.ts`, `Deferred.ts`, `Layer.ts`, `internal/layer.ts`.

Row distribution by kind, and by cited file:

| Kind | Rows | | File | Rows |
|---|---|---|---|---|
| `op` | 17 | | `internal/effect.ts` | 76 |
| `layer` | 16 | | `Layer.ts` | 15 |
| `scope` | 14 | | `Deferred.ts` | 12 |
| `fork` | 12 | | `internal/core.ts` | 10 |
| `deferred` | 12 | | `Ref.ts` | 9 |
| `rule` | 10 | | `Scheduler.ts` | 8 |
| `ref` | 10 | | `Array.ts` | 2 |
| `cause` | 10 | | `Scope.ts`, `Cause.ts`, `Exit.ts`, `MutableRef.ts`, `internal/layer.ts` | 1 each |
| `scheduler` | 9 | | | |
| `frame-arm` | 9 | | | |
| `entry` | 8 | | | |
| `checkpoint` | 6 | | | |
| `interrupt`, `exit` | 2 each | | | |

`Effect4Test/Audit/RuntimeCoverage.lean` (4,007 lines) joins those 137 rows to Lean witnesses
through **814 witness entries**. The frozen row list begins at `:4946`; the gate's pinned totals
are `expectedRowTotal := 137` and `expectedDenominator := 135`
(`Effect4Test/Audit/RuntimeCoverage.lean:6695-6696`, enforced at `:6728` and `:6781`).

| Field | Value |
|---|---|
| Rows | 137 |
| Denominator | 135 (2 `targetOnly` rows excluded) |
| `green` | **134** |
| `partial` | **1** |
| `absent` | 2, and both are the excluded rows |
| Dispositions | `separateCalculus` 121, `owned` 6, `derivedExpansion` 5, `foreignBoundary` 3, `targetOnly` 2 |

The single `partial` row is `op.Failure` (`:4954`); its missing clause is the cause annotation
with the current stack frame, which needs a fiber `Context` and a `StackTrace` service key. The
two `absent` rows are `scheduler.host-loop` (`:5656`) and `entry.with-error-reporting`
(`:5765`), both `targetOnly` and therefore out of the denominator. The six `owned` rows are
`frame-arm.OnExit` (`:5073`), `frame-arm.SetInterruptible` (`:5086`),
`checkpoint.set-fiber-interruptible` (`:5135`), `interrupt.unsafe-entry` (`:5151`),
`fork.join` (`:5367`), and `rule.record-and-apply-separate` (`:5895`).

The module fails the build on a missing witness, a non-theorem witness, an axiom-receipt drift,
a duplicate id, or an inconsistent disposition/coverage pairing (`:20-26`), and the exact
propositions are frozen by `#check` ascription (`:44-46`).

**The conclusion that matters for planning: the fiber-runtime census is essentially closed.**
134 of 135 in-denominator rows are green, including all 10 `ref.*`, all 12 `deferred.*`, and all
16 `layer.*` rows. The next unit of work in this repository is not deepening the core; it is
widening the census to files it has never covered.

Two documents disagree with the code on this point and should be treated as stale rather than
as evidence. `PORT-MANIFEST.md:770` asserts that the 38 `ref.*`, `deferred.*`, and `layer.*`
rows are absent "because the destination modules named below are still breadth stubs with no
declaration", and names `Effect4/Stateful/Ref.lean` and `Effect4/Stateful/Deferred.lean`, which
do not exist; the witnesses in fact come from `Effect4/Deep/Stores.lean` and
`Effect4/Deep/Layer.lean`. `docs/RUNTIME-COVERAGE.md`'s "Path to full coverage" table likewise
still lists those families as owed. Both predate the 2026-09-04 Deep promotion, and neither is
checked by a gate.

**Quoting discipline.** The figures above were read off the frozen row list and agree with the
module's own pinned constants, but the sanctioned coverage number is the output of
`scripts/report-effect-runtime-coverage.sh` run after `scripts/check-effect-runtime-census.sh`
passes. Any report that publishes a coverage percentage should run the script rather than cite
this section. Note also that the working tree currently has uncommitted changes, which the
script reports on its commit line.

### 2.2 The Deep machine

`Effect4/Deep/` is 8,913 lines across six modules: `Fibers.lean` (1,279),
`Stores.lean` (1,611), `Layer.lean` (2,078), `ForkFlow.lean` (1,754), `Context.lean` (1,164),
`Witnesses.lean` (1,027).

`Fibers.lean` already models the dispatcher faithfully:
`Bucket` is "buckets in ascending priority, FIFO within a bucket", cited to
`Scheduler.ts:105-131` (`Effect4/Deep/Fibers.lean:114-119`); `Dispatcher` carries
`buckets` and an `armed` flag cited to `Scheduler.ts:188-233` and `:207-212`
(`Effect4/Deep/Fibers.lean:120-126`). Four of its cites were re-read against the pin and all
four land exactly: `internal/effect.ts:5277` is the deferred child start,
`:986` is the yield resume, `:1121` is the synchronous async resume, `:552-555` is the lazy
dispatcher getter.

Critically, `Task` has exactly **two** constructors, `start` and `resume`, with the comment
"Everything else resumes synchronously through `resume(effect)`"
(`Effect4/Deep/Fibers.lean:106-112`). Measured against the seven-site table in section 1.6,
that comment is true of the *modelled subset* and false of the library: sites 3 through 7
(`Latch`, `Queue`, `Semaphore`, `Pool`, STM) each enqueue a task shape the Deep alphabet has
no constructor for. **Extending `Deep.Fibers.Task` is the single shared prerequisite for every
component proposed below.**

`Stores.lean` carries `RefHeap`, `DeferredStore` (`:653-671`), `ScopeStore` (`:859-874`), and
the composite `Stores` (`:1002-1012`), with 61 theorems. `Fibers.lean` carries `RunFiber`
(`:162`), `WithFiberAction` (`:263`, 18 constructors), `RunEvent` (`:313`, 24 constructors),
`Race` (`:347`), `RunMachine` (`:357`), `RunInterp` (`:394`), `Cmd` (`:534`, 5 constructors),
`RunDecision` (`:370`, the 7 host choices), and `drive`/`stepDecision` (`:1064`, `:1147`). It
proves nothing itself; the 53 executable witnesses live in `Effect4/Deep/Witnesses.lean`, each
a `Deep.Stores` program run through `replayEval` on an explicit decision tape and closed by
`decide`.

Two caveats for anyone reading the Deep sources. The module docstrings still describe a
non-default `Deep` library built from `srcDir = "workshop"`; that is **stale**, since all six
modules are imported by `Effect4.lean` and `lakefile.toml` has no `Deep` target. And
`Effect4/Deep/Context.lean` says `Context.ts` is not vendored, whereas
`vendor/effect-4.0.0-rc.112/src/Context.ts` exists and matches the pin.

### 2.3 The family rows and the house idiom

A "family row" is one `OpRow` inside a `ServiceRow`
(`Effect4/Target/TypeScript/EffectV4.lean:165`), emitted by the `effect_signature` command
elaborator in `Effect4/Meta/Derive.lean`. An `OpRow` carries `name`, `index`, Lean and
TypeScript parameter spellings, Lean and TypeScript answer spellings, cues, a `pure` flag, an
optional aborting-error pair, and an answer arity. One `effect_signature` declaration emits the
name and parameter enums, the `Effects.Family` instance, the signature, one smart constructor
per verb, the `rows : ServiceRow` value, and the trace face (`spelling`, `encodeParam`,
`encodeAnswer`, `traced`). An opaque host object crosses as `Handle "TypeScriptType"`, whose
carrier is a stable index; a closure crosses as an index into a named-function table declared by
`effect_atoms`.

Verb coverage per family:

| Family | Module | Rows | Verbs |
|---|---|---|---|
| `Refs` | `Effect4/Stateful/RefFamily.lean:219` | 12 | `make`, `get`, `set`, `getAndSet`, `setAndGet`, `update`, `getAndUpdate`, `updateAndGet`, `modify`, `getAndUpdateSome`, `updateSomeAndGet`, `modifySome`. Plus `ERefs` (3 aborting rows). `updateSome` and `getUnsafe` deliberately unrowed. |
| `Deferreds` | `Effect4/Stateful/DeferredFamily.lean:118` | 16 | `make`, `succeed`, `fail`, `isDone`, `poll`, `awaitValue`, `awaitError`, `awaitDeferred`, `failCause`, `die`, `interrupt`, `interruptWith`, `complete`, `completeWith`, `done`, `into`. |
| `Scopes` | `Effect4/Runtime/ScopeFamily.lean:304` | 16 | `make`, `addFinalizer`, `remove`, `close`, `makeWith`, `fork`, `addFinalizerExit`, `closeExit`, `isClosed`, `closedWith`, `provide`, `use`, `forkIn`, `runIn`, `linked`, `exitFiber`. |
| `Layers` | `Effect4/Layer/LayerFamily.lean:158` | 22 | `succeed`, `effect`, `scoped`, `provide`, `provideMerge`, `merge`, `mergeAll`, `fresh`, `memoize`, `orDie`, `unwrap`, `makeMemoMap`, `forkMemoMap`, `build`, `buildWithScope`, `buildWithMemoMap`, `launch`, `servicesOf`, `scopeOf`, `provideCount`, `observers`, `close`. |
| `Contexts` | `Effect4/Context/ContextFamily.lean:115` | 20 | `empty`, `key`, `referenceKey`, `make`, `add`, `get`, `getOption`, `merge`, `mergeAll`, `pick`, `omit`, `provideContext`, `updateContext`, `withContext`, `keyConflict`, `maxOpsBeforeYield`, `preventSchedulerYield`, `currentMemoMap`, `currentScope`. |
| `Fibers` | `Effect4/Deep/ForkFlow.lean:239`, `Effect4/Target/TypeScript/FiberProfile.lean:336` | 12 | **Not an `effect_signature`.** `FiberFamily` was retired 2026-09-04; the verbs live as `OpSpec` rows: `fork`, `forkScoped`, `join`, `awaitFiber`, `interruptFiber`, `interruptAll`, `childrenSnapshot`, `awaitChildren`, `raceAll`, `uninterruptibleIn`, `interruptibleIn`, `yieldNow`. |

`ContextFamily.lean` cites `Scheduler.ts:269-272` and `:295-298` for the two scheduler
references and their defaults `2048` and `false` (`Effect4/Context/ContextFamily.lean:46-47`,
`:85`, `:166-169`), which agrees with the pin.

The store-side spelling that a `Queue` model would mirror is separate from the family row.
`Effect4/Stateful/RefFamily.lean` also declares the opaque handle
`abbrev RefHandle := Handle "Ref.Ref<number>"` (`:150`), the named-function table `RefFn`
(`:132-143`), and the verb enum `RefOp` (`:268-281`). A new component needs both faces: an
`effect_signature` family for the traced boundary, and a store-side state plus step for the
proofs.

### 2.3.1 The links

`Effect4/StdLib/Links.lean` declares 65 `Link`s from census paths `[module, name]` to
`ModelRef`s, where a `ModelRef` is a family row, a `Prim` constructor, a `WithFiberAction`, or a
`Deep.Stores.SyncOp`. `Link.checked` verifies both that the path resolves in the store and that
every reference names something declared; `Effect4Test/Arch/ArchContract.lean:119-120` guards
`links.all Link.checked` and `links.length = 65`. By module: Effect 26, Layer 13, Context 9,
Ref 7, Fiber 5, Deferred 4, Scope 1. Against 1,835 census exports that is roughly 3.5% of the
pinned surface carrying a declared model reference. The coverage claim of record is the 137-row
census, not this ratio, but the ratio is the honest measure of how much of the library has been
looked at.

### 2.4 What is **not** reified

This was checked independently of any prior summary, by grepping the whole Lean tree (219
modules under `Effect4` and `Effect4Test`):

| Component | Lean files mentioning it | Verdict |
|---|---|---|
| `Queue` | 7 | **No semantic model.** Five hits are the unrelated `Handle "JobQueue"` fixture in `Effect4Test/Counterexamples/Target/JobRequest.lean`; the rest are export-census rows in `Effect4/StdLib/Rc112.lean:1224-…`. |
| `PubSub` | 1 | **No model.** `Effect4/StdLib/Rc112.lean` only. |
| `Stream` | 1 | **No model.** Census only. |
| `Sink` | 1 | **No model.** Census only. |
| `Channel` | 5 | **No model.** All five hits are `errorChannel`/`requirementChannel` string builders in `Effect4/Target/TypeScript/*Lower.lean`. |
| `Semaphore` | 0 | **Absent.** |
| `Latch` | 0 | **Absent.** |
| `Pool` | 0 | **Absent.** |
| `RcMap` | 0 | **Absent.** |
| `MutableList` | 0 | **Absent.** |
| `Schedule` | 18 | **Absent as a component.** Every hit is `Scheduler.ts` (the fiber scheduler), not `Schedule.ts`. |

`Semaphore`, `Pool`, `RcMap`, and `Cache` are stronger cases still: they have **zero occurrences
anywhere in the repository**, including the 1,835-row export census, which does not reach those
modules. `Schedule` has 39 export-census rows but no model; all 509 Lean hits for the string
"Schedule" are `Scheduler`, `scheduled`, or `scheduling`, and a regex excluding those returns
nothing.

Consistent with this, **none of the ten has a runtime-census row**, and none of
`Queue.ts`, `PubSub.ts`, `Stream.ts`, `Channel.ts`, `Sink.ts`, `Semaphore.ts`, or `Schedule.ts`
is vendored (section 4.9).

Additionally, no notion of a **delivery grade** (`noLoss` / `noDup`) exists anywhere in either
`lean4-effect4` or `effect-nats-verified`. In the latter the nearest equivalents are separate
named theorems (`visible_global`, `visible_sequences_strict`, `lagged_iff`). The grade is a new
piece of vocabulary the registry must define, not import.

One near-miss worth naming so it is not mistaken for prior art: `Effect4Test/Flow/JobRunnerContract.lean:42`
declares a `structure Queue`, but it is an unrelated three-field test fixture with `pending` and
`failures`, not a model of `Queue.ts`.

### 2.5 What `effect-nats-verified` already settles about `Queue`

It models a **restricted** `Queue`: `structure EffectQueue { buffer : List StoredMessage,
status : QueueStatus, taker : Bool }`, with `QueueStatus = opened | closing e | done e |
shutDown`, and verbs `empty`, `size`, `offer`, `fail`, `shutdown`, `takeAll`, `wake`. Proved:
`takeAll_drains`, `takeAll_closing`, `fail_empty`, `fail_nonempty`, `exit_after_drain`,
`shutdown_clears`, `size_eq_length`, `offer_admits`, `offer_refused`.

Its README declares the Effect `Queue` itself out of scope, and the model deliberately
abstracts away: a single boolean `taker` rather than a set; no `offers` set (parked offers are
the unreachable `wouldSuspend` outcome, the declared stage-B1/B2 boundary); no
`awaiters`; no `capacity` mutation; no `dispatcher`; no strategies other than suspend; no
`peek`, `poll`, `clear`, `takeBetween`, `into`. A full `Queue` component is therefore not a
duplication of that work but its completion, and the two must be related by an erasure, in the
same style as its own `eraseRt`.

---

## 3. Ranking the unreified components as starting points

The five criteria are: (a) verb-set size, (b) self-containment of state, (c) meaningfulness of
a delivery grade, (d) how much of the library sits on top, (e) availability of fixtures.

### 3.1 The dependency order

Measured from the imports, the stack is:

```
Scheduler/dispatcher
  └─ Fiber (run loop, stack, interrupt)
       ├─ Scope ─ Layer ─ Context
       ├─ Deferred ─ Latch ─ Semaphore
       │              └─ SynchronizedRef, SubscriptionRef, Pool, RcMap
       ├─ Queue ─┐
       └─ PubSub ─┴─ Channel ─ Stream ─ Sink
```

`Channel.ts:26-53` imports `PubSub`, `Pull`, `Queue`, `Latch`, `Semaphore`, `Scope`, `Layer`,
`Schedule`, `MutableRef`. `Stream.ts:45` imports `Queue`. `Sink.ts:31` imports `Queue`.
Nothing in the stable tree sits below `Scheduler`.

### 3.2 The ranking

| Rank | Component | (a) verbs | (b) self-contained | (c) grade | (d) load-bearing | (e) fixtures | Verdict |
|---|---|---|---|---|---|---|---|
| 1 | **Semaphore** | 10, all in one 115-line class | Yes: three scalar/set fields, no scope, no sub-object | Not delivery; the grade is a **fairness/safety** grade (`taken <= permits` when never resized; barging admitted) | `withPermits` gates `Channel.toPull`, `SynchronizedRef`, `SubscriptionRef`, `Pool`, `PartitionedSemaphore` | 3 doctests in `Semaphore.ts`; no smol test file (module did not exist at `b9da199`) | Best first move. Smallest closed verb set in the library that still exercises a scheduled task. |
| 2 | **Latch** | 11, one 90-line class | Yes: two arrays and a boolean | Not delivery; a **wake-up** grade (no lost wake-up, no double wake-up) | `Channel.mergeAll` (`Channel.ts:8125`), `Effect.ts:4244-4267` | Doctests in `Latch.ts`; no smol test file | Cheap, and it is the cleanest possible isolation of the "same verb, sync vs scheduled" question. |
| 3 | **Queue** | 26 public, 9 internal | Yes: six fields, one union, one `MutableList` | **Yes**, and it is the canonical case | Everything in Stream/Channel/Sink, Pool, and 18 `unstable/` modules | 37 doctests; `effect-smol` `Queue.test.ts` (191 lines, 13 blocks), stale | The owner's chosen anchor. Already half-done in `effect-nats-verified`. |
| 4 | **MutableList** | 12 | Yes: pure data, no effects at all | No | `Queue.messages`, `PubSub` pollers and publishers | Doctests only | A prerequisite lemma library for `Queue`, not a component in its own right. |
| 5 | **PubSub** | ~20 public plus 4 backing classes and 3 strategy classes | **No**: owns a `Scope`, a `Latch`, a `MutableRef`, and `Deferred`s | **Yes**, but with the zero-subscriber caveat I-P1 | `Stream.fromPubSub`, `SubscriptionRef`, `Channel.toPubSub`, broadcast/share | 38 doctests; `PubSub.test.ts` (479 lines, 24 blocks), stale | High value, high cost. Four backing implementations must either be proved equivalent or modelled as one. |
| 6 | **Pool** / **RcMap** | ~15 each | Partly: both own a `Scope` and reference counts | A **lease** grade | `RcMap` under `Stream.groupBy`; `Pool` standalone | `Pool.test.ts` 423 lines/21 blocks, `RcMap.test.ts` 179/13, stale | Both are reference-counting machines isomorphic to the `Layer` memo map, which is already 16 census rows. Do them after `Layer`. |
| 7 | **Channel / Stream / Sink** | Hundreds | Yes in the sense that they add *no* state | Only compositionally | The top of the stack | 145 + 529 + doctests; smol tests 27 + 10 + 9 blocks | **Do not model as a state machine.** They are a function algebra; the right artifact is a compositional grade calculus (section 4.7). |
| 8 | **Schedule** | opaque | No | No | retry/repeat everywhere | 12 smol blocks | Deferred. `Schedule` is a branded pipeable with no public opcode union, so there is nothing to reify without inventing one. |

### 3.3 The recommended cut

**Semaphore, Latch, Queue**, in that order, then **PubSub**. The first two are cheap, are
genuinely new (zero Lean files mention them), and between them they force the two shared
infrastructure changes that `Queue` also needs: the extra `Task` constructors and the
scheduled-versus-synchronous wake-up distinction. Doing them first means `Queue` lands on
infrastructure that has already been exercised.

### 3.4 Fixtures

The pinned package contains **no test directory**. What it does contain is **5,879
`import.meta.vitest` doctest blocks** across the source tree, each an executable program with
its expected value written as a `// =>` comment. Per module: `Stream.ts` 529, `Effect.ts` 526,
`Channel.ts` 145, `Layer.ts` 71, `Cause.ts` 63, `SubscriptionRef.ts` 60, `Deferred.ts` 47,
`PubSub.ts` 38, `Queue.ts` 37, `Scope.ts` 17, `Semaphore.ts` 3. These are the highest-quality
fixture source available because they are **pinned**: they live in the same file whose hash the
registry records, so a fixture cannot silently drift from the code it tests.

`effect-smol` has a real test tree (`Queue.test.ts` 191 lines, `PubSub.test.ts` 479,
`Layer.test.ts` 357, `Pool.test.ts` 423, `Stream.test.ts` 370, `Effect.test.ts` 1,550), but its
head is 2025-09-21 and its `Queue.ts` differs from the pin by 197 code lines. Those tests are
**candidate** fixtures: each must be re-run against the pin before it is admitted, and any that
fails is itself a finding.

---

## 4. Proof infrastructure

### 4.1 Per component

Each registry entry needs seven artifacts. The house style already supplies the shape for five
of them.

| Artifact | Form | Precedent |
|---|---|---|
| State type | `structure` with one field per mutable field of the JS object, plus opaque `Handle "…"` for host references | `Effect4/Deep/Stores.lean:653-671` (`DeferredStore`), `RefFamily.lean:150` |
| Label type | `inductive` verb enum over *internal* verbs, with public verbs derived | `Effect4/Stateful/RefFamily.lean:268-281` |
| Step | `def step : State → Label → Option (State × Val)`, total-or-disabled so traces are `decide`-checkable | `effect-nats-verified` `rtStep : RtState → RtLabel → Option RtState` |
| Reachability | `inductive Reachable : State → Prop` with `init` and `step` | `effect-nats-verified` `ReachableRt` |
| Invariant | one `structure Inv` per component, one theorem `inv_reachable` | `effect-nats-verified` `rtInv_reachable`; `Effect4/Deep/Witnesses.lean` |
| Trace projection | `def observe : State → Obs`, and the grade stated over `observe` | new |
| Fixture exporter + replay | a deterministic `List Trace` printed as JSON, replayed by both faces | `effect-nats-verified` `Main.lean`; `harness/trace/*` in this repo |
| Family row | an `effect_signature` declaration giving the traced boundary | `Effect4/Stateful/RefFamily.lean:219` |

The step artifact has three sanctioned spellings in this tree, and the choice is determined by
whether the model has an external decision source:

1. **Total function** `step : State → Label → State`, when there is no decision source.
   `FrameFiber.step` in `Effect4/Runtime/Runtime.lean` is the canonical instance, and its
   docstring says why: with no decision source, `docs/DESIGN-BASIS.md` DB-03's relational
   requirement does not apply. `Semaphore`, `Latch`, and `Queue` all have decision sources
   (the dispatcher), so this spelling does **not** apply to them.
2. **Executable `stepEval` plus a one-line `Prop` relation on top**, when a decision tape
   exists. Both `Effect4/Concurrency/Scheduler.lean` and `Effect4/Deep/Fibers.lean` use it, and
   the relation is always a `def … : Prop` of the form `after = stepDecision interp fuel before
   decision`, never an `inductive`. Above it sits a `replayEval` with three arms,
   `finished` / `frontier` / `stuck`, where exhaustion is a live frontier rather than a failure.
   **This is the spelling the three proposed components should use.**
3. **A record of named operations plus a separate parameter record giving the names meaning**
   (`PrimInterp`, `RunInterp`). This is design basis DB-02: nothing function-valued ever enters
   a carrier, so every carrier keeps `DecidableEq` and every witness can close by `decide`.

Five further conventions are load-bearing and a new module must satisfy them:
`deriving DecidableEq` on every carrier; a `path:line` citation into the pin in every arm's
docstring; a `census: <row-id>` docstring trailer joining a theorem to its census row; a
`cases_receipt` theorem per closed alphabet (the idiom that freezes "there is no eighteenth
primitive"); and **refusals stated as named theorems rather than comments**
(`key_freshness_refused`, `withFiber_refused`, `layerId_identity_not_structural`). The axiom
ceiling is `propext` and `Quot.sound` only, enforced by `Effect4Test/Audit/AxiomGate.lean`,
which tokenizes authored sources so a `sorry` inside an `example` cannot hide, and requires
that a cited receipt be a named `theorem` rather than an `example` so it leaves a constant for
`#print axioms` and the census join.

### 4.2 Shared: the delivery grade

Neither repository defines one. Proposed shape, stated once and instantiated per component:

```
Grade (C : Component) (F : FailureModel) :=
  { noLoss : every value admitted by an accepting verb is either observed by
             some consuming verb or accounted for by a label in F
  , noDup  : no value is observed twice
  , order  : the observed sequence is a subsequence of the admitted sequence }
```

The failure model `F` is the label set that is allowed to lose: for `Queue`, `F` is
`{shutdown, sliding-overflow, dropping-refusal, interrupt-of-a-parked-offerer}`; for `PubSub`,
`F` additionally contains `publish-with-no-subscribers` (I-P1) and `slide`. Stating `F` as a
label set rather than a probability makes the grade a theorem rather than a benchmark, and makes
"where a queue is used" (the section 1.3 table) into a composition rule: a `Stream` combinator's
grade is the join of the grades of the queues it allocates.

### 4.3 Modelling scheduled tasks and microtasks

The Deep machine already has the right structure and it should be reused rather than
duplicated: `Bucket` (ascending priority, FIFO within) and `Dispatcher { buckets, armed }`
(`Effect4/Deep/Fibers.lean:114-126`). Three changes are needed.

1. **Extend `Task`.** It currently has two constructors (`Effect4/Deep/Fibers.lean:109-112`).
   The library has seven task shapes (section 1.6). At minimum add
   `releaseTakers (q : QueueHandle)`, `flushLatch (l : LatchHandle)`, and
   `sweepPermits (s : SemHandle)`. Keeping the alphabet closed and finite is what preserves
   `decide`-checkable traces.
2. **Model the guard, not just the queue.** `Queue.scheduleRunning` (`Queue.ts:1970-1973`) and
   `Latch.scheduled` (`internal/effect.ts:5581-5587`) are *coalescing* guards: a second
   schedule while one is pending is a no-op or an append, not a second task. A model that
   enqueues unconditionally will produce traces the runtime cannot.
3. **Model dispatcher identity.** `Queue` stores its dispatcher at construction
   (`Queue.ts:455`); everything else reads `fiber.currentDispatcher`
   (`internal/effect.ts:553-555`). The `Dispatcher` must therefore be addressable, not a
   singleton field of the machine.

**Microtasks** need no separate carrier. The only place they appear is `MixedScheduler`'s
`"sync"` mode (`Scheduler.ts:95-103`, `:161`), and the only consumer of that mode is
`runSyncExitWith`, which immediately calls `flush()` (`internal/effect.ts:5541-5543`).
`flush` cancels the pending host callback and drains synchronously (`Scheduler.ts:238-246`).
So under `runSync` the microtask never runs, and the model can treat `flush` as a pure
fixpoint over the bucket list. That is the replay determinism lever: **fixtures are recorded
under `runSync`, where the host queue is provably empty.** Under `runFork`/`runPromise` the
host boundary is genuine nondeterminism and should be modelled as an oracle choosing when to
drain, with the theorem quantified over all such choices.

### 4.4 Modelling interruption across a component boundary

Every parking verb in the library returns a cleanup effect from its `Async` registration, and
`asyncFinalizer[contE]` runs it exactly when the cause carries an interrupt
(`internal/effect.ts:1156-1159`). The uniform model is therefore:

- A parked entry is a pair `(handle, cleanup : Label)` where `cleanup` is a *component* label,
  not an effect: `Queue.removeTaker`, `Queue.removeOffer` (`Queue.ts:2077-2082`, `:2010-2015`),
  `Deferred.removeResume` (`Deferred.ts:178-186`), `Semaphore.removeObserver`
  (`Semaphore.ts:218-221`), `Latch.removeWaiter` (`internal/effect.ts:5624-5637`).
- Interrupting a fiber parked on component `C` fires exactly one `C`-cleanup label, then
  resumes the fiber with the interrupt cause.
- The boundary theorem to prove for each component is **cleanup completeness**: after the
  cleanup label, the component's state contains no reference to the interrupted fiber. This is
  the property that composes, because it is what lets a `Stream` proof forget the interrupted
  fiber entirely.

Two asymmetries must be reproduced rather than smoothed. First, the cleanup effects guard on
state: `Queue.awaitTake`'s cleanup deletes only `if (self.state._tag !== "Done")`
(`Queue.ts:2079`), and `offerRemainingSingle`'s only `if (self.state._tag === "Open")`
(`Queue.ts:2011`), so a finalized component performs no cleanup at all and relies on
`finalize` having already cleared the sets (`Queue.ts:2106-2112`). Second, `PubSub` does not use
the `Async` cleanup channel; it uses `Effect.onInterrupt` around a `Deferred.await`
(`PubSub.ts:1452-1458`), which fires on a different code path.

### 4.5 Modelling `Scope` finalizer ordering

`Scope` is already 14 census rows plus `Effect4/Runtime/Scope.lean`, `ScopeMachine.lean`,
`ScopeRestoration.lean`, `ScopeFamily.lean`, and `Effect4/Deep/Stores.lean:859-874`. What a
component registry additionally needs from it is a **narrow interface**, not a re-model:

- `finalizers : List (Key × (Exit → Label))`, insertion-ordered.
- `close(exit)` fires them in reverse (`internal/effect.ts:3815`).
- The three fast paths of `scopeCloseUnsafe` are *not* an optimization to be normalized away:
  the lone-finalizer path returns the finalizer's own effect directly (`:3788-3790`,
  `:3794-3796`) while two or more go through `exitAsVoidAll` (`:3826`). Model
  `close` with a case split on `|finalizers| ∈ {0, 1, ≥2}` and prove the aggregation lemma
  separately.
- `fork` installs the mutually cancelling pair (I-S3, `:3840-3842`), and the theorem to prove
  is that the pair leaves no entry behind on either close order.

The `parallel` strategy forks daemon children (`:3820`) and is therefore where scope ordering
becomes genuinely nondeterministic; the sequential strategy is the deterministic default
(`internal/effect.ts:3915`) and should be the first thing proved.

### 4.6 Strategies: parameters, not components

`"suspend" | "dropping" | "sliding"` is a `Queue` **field** branched on inline at
`Queue.ts:648-664`, `:711-721`, `:815-826`. Model it as a parameter of the step relation. The
payoff is that a single `Queue` invariant proof is parametric in the strategy, and the three
grades differ only in their failure-model label sets: `suspend` has an empty overflow label,
`dropping` has `refuse`, `sliding` has `evictOldest`.

`PubSub` is the opposite case. There the strategy is a genuine object with mutable state:
`BackPressureStrategy` owns a `MutableList` of parked publishers
(`PubSub.ts:2715-2717`), and `handleSurplus` allocates a `Deferred` per surplus batch
(`PubSub.ts:2735-2745`). `DroppingStrategy` (`PubSub.ts:2854-2890`) and `SlidingStrategy`
(`PubSub.ts:2937-…`) are stateless. So for `PubSub`, model `Dropping` and `Sliding` as
parameters and `BackPressure` as a **component in its own right** with its own state and
verbs.

### 4.7 Channel, Stream, and Sink: a grade calculus, not a machine

Since `Channel` adds no state (section 1.3), the right artifact is a judgement
`Γ ⊢ c : Grade` where `Γ` assigns grades to the queues and pubsubs a combinator allocates, plus
composition rules for `pipeTo`, `flatMap`, `merge`, and `mapEffect`. The section 1.3 allocation
table is the seed of `Γ`. This is substantially cheaper than a state machine and is the only
form in which a claim about `Stream` can be stated at all, given that `Stream.ts` is 20,442
lines of combinators over one field.

### 4.8 Shared infrastructure to build once

1. `MutableList` as a lemma library: it is a `List` with a cached length and a bucket
   structure (`MutableList.ts:35-38`). Prove `length` agrees with the flattened list once, and
   every `Queue` proof can work with `List`.
2. The extended `Deep.Fibers.Task` alphabet and the coalescing-guard discipline (section 4.3).
3. The parked-entry-with-cleanup-label pattern (section 4.4).
4. `Grade` and `FailureModel` (section 4.2).
5. A census-row generator for the new files. The existing generator
   (`scripts/generate-effect-runtime-census.sh`, hash recorded at
   `generated/effect-runtime-census.tsv:2`) already emits
   `mechanism | kind | id | file | lines | span-sha256 | summary`, which is exactly the PINS
   format the registry wants. Extending its input list is a smaller change than writing a new
   tool.

### 4.9 The order in which a new component must land

The four artifacts are cross-checked by the coverage gate, so they have to be added in this
order or the build fails:

1. **Vendor the file.** `vendor/effect-4.0.0-rc.112/src/` currently holds only twelve modules
   plus `internal/`. `Queue.ts`, `PubSub.ts`, `Semaphore.ts`, `Stream.ts`, `Channel.ts`,
   `Sink.ts`, and `Schedule.ts` are all absent, so the census generator, which refuses
   non-pinned bytes, **cannot be pointed at them today**. `Latch` is the exception: it lives
   inside `internal/effect.ts:5568-5651`, which is already vendored, so `Latch` needs no
   vendoring step at all. That is a second, independent reason to do `Latch` early.
2. **Extend the generator's input list and emit the new spans.**
3. **Add `PORT-MANIFEST.md` disposition rows.** The nine-value vocabulary is fixed
   (`owned`, `split`, `downstreamAdapter`, `separateCalculus`, `derivedExpansion`,
   `foreignBoundary`, `targetOnly`, `evidenceOnly`, `excludedInternal`). `PORT-MANIFEST.md:759`
   already pre-assigns family defaults for `Queue`, `PubSub`, `Stream`, `Channel`, `Sink`, and
   `Schedule`, so the disposition question is partly settled; `PLAN.md:46` names `Queue` in
   packet P7.
4. **Add `RuntimeCoverage.lean` rows** with their witnesses and `#check` ascriptions, and bump
   `expectedRowTotal` and `expectedDenominator`
   (`Effect4Test/Audit/RuntimeCoverage.lean:6695-6696`).

Adding rows before witnesses exist is legitimate and is how the census is meant to be used: a
row with `coverage := "absent"` and an empty witness list is a recorded obligation. Given that
the current denominator is 134 green out of 135, the honest effect of vendoring `Queue`,
`Semaphore`, `Latch`, and `PubSub` is that the published coverage percentage **falls sharply**
before it rises. That is the correct behaviour and should be stated in advance rather than
discovered.

---

## 5. Concrete starting plan

`Queue` is taken as given. The first three components after it, in order.

### 5.1 First: `Semaphore`

**Why first.** Ten verbs in a 115-line class; three fields, no sub-objects, no scope; zero Lean
files mention it; and it exercises a scheduled task, which forces the shared infrastructure
change before `Queue` needs it.

**State.** `{ permits : Int, taken : Int, waiters : List (FiberId × Nat) }`. `Int`, not `Nat`:
`resize` can make `free` negative (section 1.7).

**Verbs and pins.**

| Verb | Pin |
|---|---|
| `waitForPermits` (park, with removal-on-interrupt) | `Semaphore.ts:207-224` |
| `take` | `Semaphore.ts:238-247` |
| `takeIfAvailable` | `Semaphore.ts:249-255` |
| `releaseUnsafe` (decrement + schedule sweep) | `Semaphore.ts:257-267` |
| `sweep` (the scheduled task body) | `Semaphore.ts:260-265` |
| `resize` | `Semaphore.ts:270-277` |
| `release` | `Semaphore.ts:279-281` |
| `releaseAll` | `Semaphore.ts:283-285` |
| `withPermits` (uninterruptible mask, acquire, `onExitPrimitive` release) | `Semaphore.ts:287-307` |
| `withPermitsIfAvailable` | `Semaphore.ts:311-320` |
| `removeObserver` (interrupt cleanup) | `Semaphore.ts:218-221` |

**Failure-model labels.** `{ interruptDuringWait, resizeShrink }`.

**Expected grade.** Not a delivery grade. The three theorems are:

- **Safety.** `taken <= permits` on every reachable state, given no `resize` shrink below
  `taken`. Provable.
- **Release soundness.** `withPermits n` releases exactly `n`, exactly once, on every exit path,
  because the release sits in `onExitPrimitive` with the uninterruptible flag set
  (`Semaphore.ts:296-303`).
- **Non-fairness.** There exists a reachable trace in which a waiter for `n` permits is
  overtaken by a later waiter for `m < n`. This should be proved as a **counterexample**, not
  left unproved, because the doc comment claims it (`Semaphore.ts:123-133`) and a registry that
  silently omits it invites a false FIFO assumption downstream.

**Fixtures.** 3 doctests in `Semaphore.ts`. Thin. Supplement from `Channel.toPull`
(`Channel.ts:8238-8244` at rc.111; **NOT VERIFIED** at rc.112) and from
`SynchronizedRef.test.ts` in `effect-smol` (105 lines, stale).

### 5.2 Second: `Latch`

**Why second.** It is the minimal isolation of the sync-versus-scheduled wake-up question that
`Queue` and `Semaphore` both depend on, and it is 90 lines.

**State.** `{ isOpen : Bool, waiters : List FiberId, scheduled : Option (List FiberId) }`. The
`Option` matters: `undefined` and `[]` are distinguished by `scheduleUnsafe`
(`internal/effect.ts:5581-5587`).

**Verbs and pins.**

| Verb | Pin |
|---|---|
| `scheduleUnsafe` (move waiters to scheduled, arm one task) | `internal/effect.ts:5577-5591` |
| `flushScheduled` (the task body) | `internal/effect.ts:5592-5599` |
| `flushWaiters` (swap-then-resume) | `internal/effect.ts:5600-5610` |
| `open` (Effect; defers) | `internal/effect.ts:5612-5616` |
| `release` (Effect; defers, does not open) | `internal/effect.ts:5617` |
| `openUnsafe` (synchronous flush) | `internal/effect.ts:5618-5623` |
| `await` (park, with two-array removal) | `internal/effect.ts:5624-5640` |
| `closeUnsafe` / `close` | `internal/effect.ts:5641-5646` |
| `isOpen` | `internal/effect.ts:5648-5650` |
| constructors `makeLatchUnsafe` / `makeLatch` | `internal/effect.ts:5654`, `:5657` |

**Failure-model labels.** `{ interruptDuringAwait }`.

**Expected grade.** A wake-up grade: **no lost wake-up** (every waiter registered before an
`open` is eventually resumed) and **no double wake-up** (no waiter is resumed twice). Both are
provable and both are non-trivial: the swap-before-resume discipline at
`internal/effect.ts:5601-5605` exists precisely because a resumed waiter can reentrantly close
the latch and register new waiters, and a naive model will prove a false theorem here. A third
theorem worth stating is **open/openUnsafe divergence**: there is a reachable interleaving in
which the two produce different observations, which justifies keeping both verbs rather than
identifying them.

**Fixtures.** Doctests in `Latch.ts` (426 lines, doctest count **NOT VERIFIED**, not measured).
No smol test file.

### 5.3 Third: `PubSub`

**Why third and not second.** It carries a genuine delivery grade and it is what
`SubscriptionRef` and `Stream.broadcast` rest on, but it is not self-contained: it owns a
`Scope`, a `Latch`, a `MutableRef`, `Deferred`s, and one of four backing rings. It should land
only after `Latch` and `Deferred` are settled.

**State.** `{ ring : Atomic, subscribers : Map Sub (Set Pollers), scope : ScopeHandle,
shutdownHook : LatchHandle, shutdownFlag : Bool, strategy : Strategy }`
(`PubSub.ts:64-74`), with `Atomic` first modelled as `BoundedPubSubArb`
(`PubSub.ts:1859-1957`): `{ array, publisherIndex, subscribersIndex, subscribers : Array Nat,
subscriberCount, capacity }`.

**Verbs and pins.**

| Verb | Pin |
|---|---|
| `Atomic.publish` | `PubSub.ts:1889-1907` |
| `Atomic.publishAll` | `PubSub.ts:1909-1940` |
| `Atomic.slide` | `PubSub.ts:1942-1953` |
| `Atomic.subscribe` | `PubSub.ts:1955-1958` |
| `addSubscribers` / `removeSubscribers` | `PubSub.ts:1816-1827`, `:1828-1842` |
| `makeSubscriptionUnsafe` | `PubSub.ts:1843-1858` |
| `pollForItem` (park on a `Deferred` in `pollers`) | `PubSub.ts:1439-1461` |
| `publish` (Effect) | `PubSub.ts:1004-1011` |
| `publishUnsafe` | `PubSub.ts:1065-1073` |
| `publishAll` (Effect) | `PubSub.ts:1240-1251` |
| `subscribe` (uninterruptible, forks the pubsub scope) | `PubSub.ts:1304-1315` |
| `unsubscribe` (uninterruptible) | `PubSub.ts:1317-1350` |
| `take` | `PubSub.ts:1371-1389` |
| `takeAll` | `PubSub.ts:1419-1437` |
| `shutdown` | `PubSub.ts:757-765` |
| `BackPressureStrategy.handleSurplus` | `PubSub.ts:2729-2746` |
| `BackPressureStrategy.onPubSubEmptySpaceUnsafe` | `PubSub.ts:2749-2769` |
| `BackPressureStrategy.offerUnsafe` | `PubSub.ts:2783-2799` |
| `DroppingStrategy` | `PubSub.ts:2854-2890` |
| `SlidingStrategy` | `PubSub.ts:2937-…` |

**Failure-model labels.** `{ publishWithNoSubscribers, slideEviction, droppingRefusal,
shutdown, interruptDuringPoll, interruptDuringSurplus }`. The first is mandatory and is the
single most important fact this component contributes to the registry: `publish` returns `true`
and discards the value when `subscriberCount === 0` (`PubSub.ts:1897`, `:1912-1918`).

**Expected grade.** `noLoss` and `noDup` **relative to subscribers present at publish time**,
with `order` per subscriber. Under `BackPressure` with at least one subscriber and no
`shutdown`, all three should hold. Under `Sliding`, `noLoss` fails by construction and the
theorem is the bounded-loss statement: a subscriber misses exactly the values slid past its
index. Under `Dropping`, `noLoss` fails at the publish site instead.

**A prerequisite.** Four backing implementations exist (`PubSub.ts:1859`, `:2053`, `:2248`,
`:2405`), selected by capacity. Either prove the three bounded ones observationally equivalent
to `BoundedPubSubArb`, or scope the first registry entry to `BoundedPubSubArb` explicitly and
record the other three as open. The second is cheaper and honest; `makeAtomicBounded`
(`PubSub.ts:503-519`) is the dispatch point to cite.

**Fixtures.** 38 doctests in `PubSub.ts`; `effect-smol` `PubSub.test.ts` is 479 lines and 24
blocks, but stale by 249 code lines in `PubSub.ts` alone, so every one must be re-run against
the pin first.

### 5.4 Ordering rationale in one line

`Semaphore` buys the scheduled-task infrastructure cheaply; `Latch` buys the sync-versus-
scheduled distinction cheaply; `Queue` then lands on both and completes the
`effect-nats-verified` model; `PubSub` is the first component whose delivery grade has real
content, and it needs all three below it.

---

## 6. Explicit "not verified" list

1. `Channel.toPull`'s one-permit semaphore was cited at `Channel.ts:8238-8244` against rc.111.
   **NOT VERIFIED** at rc.112.
2. The doctest count for `Latch.ts` was not measured. **NOT VERIFIED.**
3. `UnboundedPubSub` (`PubSub.ts:2405-…`), `BoundedPubSubPow2` (`:2053-2154`), and
   `BoundedPubSubSingle` (`:2248-2330`) were located but their bodies were not read line by
   line. Their equivalence to `BoundedPubSubArb` is **NOT VERIFIED**.
4. `SlidingStrategy`'s body beyond `PubSub.ts:2937-2955` was not read. **NOT VERIFIED.**
5. `Stream.ts` (20,442 lines) and `Channel.ts` (12,352 lines) were surveyed by grep for
   allocation sites and interfaces only. The section 1.3 allocation table is complete for
   `Queue.make`/`bounded`/`unbounded` in the stable tree but was **not** cross-checked for
   `PubSub` or `Latch` allocation sites. **NOT VERIFIED.**
6. `Schedule.ts` was not read beyond its export list. The claim that it has no public opcode
   union is carried from the rc.111 brief and is **NOT VERIFIED** at rc.112.
7. The `unstable/` tree (18 modules importing `Queue.ts`) was enumerated but not read.
8. The Windows copy at `C:\Users\kokok\Dev\effect4-host\node_modules\effect` was not consulted.
   Its agreement with the mac pin is **NOT VERIFIED**.
9. `Effect4Test/Audit/RuntimeCoverage.lean`'s 137 rows were counted and their coverage and
   disposition fields tallied mechanically, and the totals agree with the module's pinned
   `expectedRowTotal` and `expectedDenominator` (`:6695-6696`). The individual witness theorems
   were **not** read. The claim that each `green` row is genuinely witnessed rests on the
   module's own gate (`:20-26`), not on independent reading. Neither
   `scripts/check-effect-runtime-census.sh` nor `scripts/report-effect-runtime-coverage.sh` was
   run in this pass, and no `lake build` was performed. **NOT VERIFIED** that the tree builds.
10. `PORT-MANIFEST.md` was read only at the two points cited (`:759`, `:770`). Its full
    disposition tables were not reviewed.
11. The claim that `Queue.ts` is line-stable rc.111 to rc.112 was verified for the nineteen
    ranges in section 0.3. The remaining seven of the twenty-six ranges cited by the design
    note were not individually re-read. **NOT VERIFIED.**
12. `PartitionedSemaphore.ts` (793 lines) was surveyed for its interface and the round-robin
    release loop (`PartitionedSemaphore.ts:144-176`) but not modelled or fully read.
