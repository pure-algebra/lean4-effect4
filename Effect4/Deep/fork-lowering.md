# The lowering side of the fork profile

Companion to `workshop/Deep/ForkFlow.lean` (spike S3 of
`docs/research/2026-09-03-deep-plan.md`). No Lean library is edited by this document; it
says exactly what the lowering would emit, what the one required change to the lowering is,
and what the host service that answers the calls looks like.

Ruling 3 (`docs/research/2026-09-03-deep-plan.md:29-36`): **the lowering emits a service
call and never `Effect.fork`.** That is a recorded refusal, restated as a row in §4.

---

## (a) What the lowering emits, operation by operation

The profile's rows are ordinary `OpSpec` rows, so the *existing* printer already spells
every one of them. `Skeleton.render` (`Effect4/Target/TypeScript/SkeletonRender.lean:96-97`)
sends a family `perform` to

```
[.constYield answer.name (Lowering.callOf rows spec request)]
```

and `Lowering.callOf` (`SkeletonRender.lean:68-71`) picks one of three shapes by the row:

* `spec.requestTy == "void"` → `Lowering.nullaryValue` (`EffectV4.lean:349-350`), an Effect
  *value*, not a call — rc.112 is already lazy;
* `spec.arity == 1` → `Lowering.performCall` on the request slot (`EffectV4.lean:354-355`);
* `spec.arity >= 2` → `performCall` on `Lowering.tupleArgs request.path spec.arity`
  (`SkeletonRender.lean:58-61`), which destructures the one request slot holding the
  right-nested product.

`ForkFlow.lean` pins the three arities that matter (`#guard` on `OpSpec.arity` of rows 0, 2
and 6), so the emitted text below is what the printer produces today, with **no printer
change at all**.

Take a service receiver `fibers` (`ServiceRow.receiver`, `EffectV4.lean:195-196`, the
decapitalised class name), a block `b1` whose request slot is `b1p0`, and a block `b0`
whose request slot `b0p0` holds the fork's four-slot product.

| Profile row | Emitted TypeScript |
| --- | --- |
| `fork` (arity 4) | `const a0 = yield* fibers.fork(b0p0[0], b0p0[1][0], b0p0[1][1][0], b0p0[1][1][1])` |
| `forkScoped` (arity 4) | `const a0 = yield* fibers.forkScoped(b0p0[0], b0p0[1][0], b0p0[1][1][0], b0p0[1][1][1])` |
| `join` (arity 1) | `const a1 = yield* fibers.join(b1p0)` |
| `awaitFiber` (arity 1) | `const a1 = yield* fibers.awaitFiber(b1p0)` |
| `interruptFiber` (arity 1) | `const a1 = yield* fibers.interruptFiber(b1p0)` |
| `interruptAll` (arity 1) | `const a1 = yield* fibers.interruptAll(b1p0)` |
| `childrenSnapshot` (request `void`) | `const a1 = yield* fibers.childrenSnapshot` |
| `awaitChildren` (arity 1) | `const a1 = yield* fibers.awaitChildren(b1p0)` |
| `raceAll` (arity 1) | `const a1 = yield* fibers.raceAll(b1p0)` |
| `uninterruptibleIn` (arity 2) | `const a1 = yield* fibers.uninterruptibleIn(b1p0[0], b1p0[1])` |
| `interruptibleIn` (arity 2) | `const a1 = yield* fibers.interruptibleIn(b1p0[0], b1p0[1])` |
| `yieldNow` (arity 1) | `const a1 = yield* fibers.yieldNow(b1p0)` |

The last three rows carry the interrupt half. `uninterruptibleIn` and `interruptibleIn`
take a plain root reference — `readonly [number, ReadonlyArray<unknown>]`, two slots — and
run that declared root's body under rc.112's `Effect.uninterruptible` / `Effect.interruptible`;
they are how a Flow masks *its own* fiber, which the machine reaches through
`WithFiberAction.setInterruptible` (`workshop/Deep/Fibers.lean:282-284`). `yieldNow` takes
the dispatcher priority and is the one row that compiles to a `Prim` constructor rather
than to a `withFiber` thunk (`Prim.yieldNowWith`, spike S1).

The four projections of the fork's request are `root`, `args`, `daemon`, `region`, in the
order `forkParams` declares them, because `requestSpelling`
(`Effect4/Target/TypeScript/ScriptFlow.lean:201-204`) nests the product to the right and
`tupleArgs` projects it back the same way — the converse pair `E4-TARGET-CE-026` pins.

The service is acquired once at the top of the generator, exactly as any other family is:
`const fibers = yield* Fibers` (`Lowering.serviceAcquire`, `EffectV4.lean:339-340`).

A caught `join` (Flow v3 `performCatch`) spells as every caught perform does
(`SkeletonRender.lean:107-111`):

```ts
const a1 = yield* Effect.result(fibers.join(b1p0))
if (Result.isSuccess(a1)) { /* value edge reads a1.success */ }
else { /* failure edge reads a1.failure */ }
```

which is why `join` carries a real `errorTy` on its row and `awaitFiber` carries `never`:
`join` resumes the child's exit *as an effect*, `awaitFiber` resumes it *as a value*.

`await` is a reserved identifier in the generated-binding profile — the same refusal
`Effect4/Concurrency/FiberFamily.lean:68-71` already records — so the rows are spelled
`awaitFiber` and (for symmetry) `interruptFiber`. `ForkFlow.lean` `#guard`s that all twelve
names pass `EffectV4.bindingName` (`EffectV4.lean:145-147`).

---

## (b) The one lowering change: a declared root as a callable entry

Today the dispatch form emits **one** exported function whose body assigns the entry
block's single parameter and enters the loop
(`Effect4/Target/TypeScript/FlowLower.lean:180-198`):

```ts
export const prog = (n: T) =>
  Effect.gen(function* () {
    const fibers = yield* Fibers
    let b0p0!: T
    let b1p0!: Fiber.Fiber<number, number>
    ...
    b0p0 = n
    let block = 0
    while (true) { switch (block) { case 0: { ... } ... } }
  })
```

A fork names a **declared root** (`RawFlow.roots`), and the host has to be able to start
that root with an argument list. The change is to make the generator's *entry point* a
parameter instead of a constant, and to add one synthetic dispatch case per root that binds
the root's parameters from the argument array:

```ts
/** Lowered from the flow `prog` over `Fibers` (dispatch form, multi-root). */
const prog__entry = (entry: readonly [number, ReadonlyArray<unknown>]) =>
  Effect.gen(function* () {
    const fibers = yield* Fibers
    let b0p0!: T
    let b1p0!: Fiber.Fiber<number, number>
    let b3p0!: number
    let block = entry[0]
    while (true) {
      switch (block) {
        // synthetic root-entry cases, one per declared root
        case 1000: { b0p0 = entry[1][0] as T;      block = 0; continue }
        case 1003: { b3p0 = entry[1][0] as number; block = 3; continue }
        // the flow's own block cases, byte for byte as today
        case 0: { const a0 = yield* fibers.fork(b0p0[0], b0p0[1][0], b0p0[1][1][0], b0p0[1][1][1]); b1p0 = a0; block = 1; continue }
        case 1: { const a1 = yield* fibers.join(b1p0); b2p0 = a1; block = 2; continue }
        case 2: { return b2p0 }
        case 3: { return b3p0 }
      }
    }
  })

export const prog = (n: T) => prog__entry([1000, [n]])
export const prog__root3 = (p0: number) => prog__entry([1003, [p0]])
export const progEntry = prog__entry
```

Why this shape and not a nested generator per root: `TypeScript.Stmt` has `scopedGen` and
`scopedGenMasked` and nothing else nested-generator-shaped
(`.lake/packages/typescript/TypeScript/Syntax.lean:106,129,133`), and a per-root generator
would have to redeclare every parameter slot. Entering the *same* loop at a different case
keeps one set of declarations and one switch, which is what makes the change small.

### The price, itemised

* **No `typescript` package bump.** Every statement above is already spellable: `Stmt.switch`
  (used by `dispatchLoop`), `Stmt.assign`, `Stmt.letInit`, `Stmt.continueTo`,
  `Decl.const` with `Expr.lambda`. The synthetic-root cases are cases of the *existing*
  `Skeleton.dispatchLoop`.
* **Two new `Skeleton` formers**, both `String`-free and both rendering through existing
  `Stmt` constructors (`Effect4/Target/TypeScript/Skeleton.lean:159-221`):
  * `letBlockIndexFrom (var : String) (entry : String)` → `let block = entry[0]`, beside
    the existing `letBlockIndex` (`Skeleton.lean:168-169`);
  * `rootParam (slot : Slot) (entry : String) (index : Nat)` → `b3p0 = entry[1][0]`.
* **One `Rule` tag**, `rule.root-entry`, **appended last** to `Rule.all` so no positional
  window moves — the four contract batteries pin `Rule.all` by index
  (`docs/research/2026-09-03-survey-target-harness.md:288-298`), and appending is the
  precedent `perform-tuple`/`perform-catch`/`branch-if` set (`COORDINATION.md:2613`,
  `:2690`).
* **One `docs/LOWERING-COVERAGE.md` row** for the new rule, and the module emitter
  (`FlowLower.flowModules?`) emitting `1 + |roots|` declarations plus the `progEntry`
  re-export instead of one.
* **Type honesty.** `entry[1]` is `ReadonlyArray<unknown>`, so each root-entry case casts.
  That cast is the wire's untyped `Val` surfacing on the host, and it is the same refusal
  packet P7 already carries for the untyped `Val` compile
  (`docs/research/2026-09-03-deep-plan.md:106-107`).

---

## (c) The host `Fibers` service over rc.112

One service class, one method per profile row, and a layer that closes over the module's own
`progEntry` so `fork` can turn a `(root, args)` pair into an Effect. Nothing here is ever
the subject of a theorem (`docs/research/2026-09-03-deep-plan.md:169`); it is a host
receipt.

```ts
import { Context, Effect, Fiber, Layer, Option, Result, Scope } from "effect"

/** Service `Fibers`: one method per operation of the fiber profile. */
export class Fibers extends Context.Service<Fibers, {
  readonly fork: (
    root: number,
    args: ReadonlyArray<unknown>,
    daemon: boolean,
    region: Option.Option<number>
  ) => Effect.Effect<Fiber.Fiber<number, number>>
  readonly forkScoped: (
    root: number,
    args: ReadonlyArray<unknown>,
    daemon: boolean,
    region: Option.Option<number>
  ) => Effect.Effect<Fiber.Fiber<number, number>>
  readonly join: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<number, number>
  readonly awaitFiber: (
    fiber: Fiber.Fiber<number, number>
  ) => Effect.Effect<Result.Result<number, number>>
  readonly interruptFiber: (fiber: Fiber.Fiber<number, number>) => Effect.Effect<void>
  readonly interruptAll: (
    fibers: ReadonlyArray<Fiber.Fiber<number, number>>
  ) => Effect.Effect<void>
  readonly childrenSnapshot: Effect.Effect<ReadonlyArray<Fiber.Fiber<number, number>>>
  readonly awaitChildren: (
    snapshot: ReadonlyArray<Fiber.Fiber<number, number>>
  ) => Effect.Effect<void>
  readonly raceAll: (
    entrants: ReadonlyArray<readonly [number, ReadonlyArray<unknown>]>
  ) => Effect.Effect<number, number>
  readonly uninterruptibleIn: (
    root: number,
    args: ReadonlyArray<unknown>
  ) => Effect.Effect<number, number>
  readonly interruptibleIn: (
    root: number,
    args: ReadonlyArray<unknown>
  ) => Effect.Effect<number, number>
  readonly yieldNow: (priority: number) => Effect.Effect<void>
}>()("Fibers") {}

/** The exit reading the wire uses: `Exit` to `Result`, the `awaitFiber` answer. */
const exitToResult = (exit: Exit.Exit<number, number>): Result.Result<number, number> =>
  Exit.isSuccess(exit) ? Result.success(exit.value) : Result.failure(Cause.squash(exit.cause))

/**
 * `enter` is the lowered module's own `progEntry` (§b). A fork therefore names a
 * declared root of the *same* flow, never an arbitrary computation.
 * `scopes` maps a region id to the `Scope` the region's generator opened.
 */
export const FibersLive = (
  enter: (entry: readonly [number, ReadonlyArray<unknown>]) => Effect.Effect<number, number>,
  scopes: (region: number) => Scope.Scope
) =>
  Layer.succeed(Fibers, {
    // rc.112 internal/effect.ts:5264-5284 (forkUnsafe), :5364-5378 (forkIn)
    fork: (root, args, daemon, region) => {
      const child = enter([1000 + root, args])
      return Option.isSome(region)
        ? Effect.forkIn(child, scopes(region.value))
        : daemon
          ? Effect.forkDaemon(child)
          : Effect.forkChild(child)
    },
    // :5400-5406 — forkIn on the ambient Scope of the calling fiber
    forkScoped: (root, args, _daemon, _region) =>
      Effect.forkScoped(enter([1000 + root, args])),
    // :5291 — the child's exit continues in this fiber as an effect
    join: (fiber) => Fiber.join(fiber),
    // :5304 — the child's exit continues as a value
    awaitFiber: (fiber) => Effect.map(Fiber.await(fiber), exitToResult),
    // :859 — record with the running fiber's id, then await the target
    interruptFiber: (fiber) => Effect.asVoid(Fiber.interrupt(fiber)),
    // :895 — record on every target first, then await them all
    interruptAll: (fibers) => Effect.asVoid(Fiber.interruptAll(fibers)),
    // :5318 — awaitAllChildren's snapshot half
    childrenSnapshot: Effect.withFiber((self) => Effect.succeed(self.children ?? [])),
    // the exit half: await the children added since the snapshot
    awaitChildren: (snapshot) =>
      Effect.withFiber((self) =>
        Effect.asVoid(
          Fiber.awaitAll((self.children ?? []).filter((c) => !snapshot.includes(c)))
        )
      ),
    raceAll: (entrants) => Effect.raceAll(entrants.map(([root, args]) => enter([1000 + root, args]))),
    // :4302-4310 / :4331-4352 — a program masking its own fiber
    uninterruptibleIn: (root, args) => Effect.uninterruptible(enter([1000 + root, args])),
    interruptibleIn: (root, args) => Effect.interruptible(enter([1000 + root, args])),
    // :982-994
    yieldNow: (priority) => Effect.yieldNow({ priority })
  })
```

Four notes the traced family will need.

1. **`fork`'s `daemon` and `region` are request fields, not formers** (review finding 14,
   `docs/research/2026-09-03-deep-plan-review.md:524-556`). `region = some n` forks a
   daemon linked to a scope, which is what rc.112's `forkIn` does anyway
   (`:5364-5378`), so the `daemon` field is only consulted when `region` is `none`.
2. **Immediacy is not a request field.** `Effect.forkChild`/`forkDaemon` decide when the
   child gets the processor; the Lean machine takes that from the decision tape
   (`RunDecision.fire`/`flush`), and `ForkFlow.forkWithFiberOf` always sets
   `startImmediately := false`. Review finding 3 is the reason.
3. **`childrenSnapshot` is a `void`-request row**, so the printer emits an Effect *value*,
   `yield* fibers.childrenSnapshot`, not a call. The service field must therefore be an
   `Effect`, not a thunk — `ServiceRow.methodType` (`EffectV4.lean:198-208`) already
   enforces that shape for nullary rows.
4. **The run-time refusal has no host counterpart, and must still be defended.** In Lean a
   request naming an undeclared root answers `WithFiberAction.refuse`
   (`workshop/Deep/Fibers.lean:295-296`) and the fiber dies with a defect. On the host the
   request is built by the compiler, so the case is unreachable — which is exactly when a
   service should `Effect.dieMessage("fork: the request names no declared root")` rather
   than silently start something. The Lean side is the one that *proves* the refusal is a
   fiber's failure and never a stuck machine (`ForkFlow.lean`, witness E).

---

## (d) The refusal row

To be added to `test/counterexamples/REGISTER.md` (or the P7 refusal list) at the landing,
verbatim:

> **The lowering emits a service call for a fork, never `Effect.fork`.** A Flow names a
> concurrent child through an operation of its supplied alphabet whose request names a
> declared root (`docs/research/2026-09-03-deep-plan.md:29-36`, ruling 3). The lowered
> program therefore contains `yield* fibers.fork(root, args, daemon, region)` and no
> `Effect.fork(Effect.gen(function*(){…}))`. Emitting `Effect.fork` needs a Flow v4 fork
> *terminator*: a new `RegionTerm` constructor (28 exhaustive matches in `Effect4/` and 9
> upstream), its own admission clauses and a re-proof of `regionWF_iff_check`, a fifth
> `ScopeName` and the re-proof of `runRegions_eq_interpret`, `RegionTotal`, `RegionSafety`
> and the region half of `Approximation`, plus a new nested-generator former in
> `TypeScript.Stmt` — i.e. a bump of **both** pinned packages
> (`docs/research/2026-09-03-deep-plan-review.md:80-101`). That is a separate, later packet
> whose only justification is emitting `Effect.fork`, and it is priced there.
>
> Consequence for reification: the generated program's fork is a *host service call*, so
> its scheduler behaviour is a host receipt and not the subject of any theorem
> (`docs/TRACE-DAG.md` `targets`). The Lean side's claim is about the machine
> (`workshop/Deep/Fibers.lean`) and the compile (`workshop/Deep/ForkFlow.lean`), not about
> the emitted TypeScript.
