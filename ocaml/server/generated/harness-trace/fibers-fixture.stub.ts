// STUB: replaced by the generated fixture
/**
 * Hand-typed stand-in for the `Fibers` fixture the L1 lowering lane generates
 * from the twelve-row profile of `Effect4/Target/TypeScript/FiberProfile.lean`
 * (`docs/research/2026-09-03-spike-s3-fork-flow.md` §2,
 * `docs/research/2026-09-03-lowering-l1-fiber-profile.md` §1-3). It exists so
 * `fibers-tail.ts` typechecks before L1 emits a *fixture*; the twelve rows,
 * their spellings and `rootEntryBase` are L1's, so the generated file replaces
 * this one without touching the tail.
 *
 * Two things this stub owns that the generator will own instead:
 *
 * - the **root table** (`fork-lowering.md` §(b)): one entry function per
 *   declared root, all of them re-entering the same dispatch loop at the
 *   synthetic case `rootEntryBase + block`. The generated module spells the
 *   same table as `prog`, `prog__root3`, … plus `progEntry`; the tail resolves
 *   a fork's `root` field through it and never through a closure.
 * - the `FibersService` interface. The generator inlines the service shape in
 *   the `Context.Service` application (L1 §2), so naming it here is a
 *   convenience of the stub; the tail imports the name and nothing else.
 */
import { Context, Effect, Option } from "effect"
import type { Fiber, Result } from "effect"

/** The service shape of the fiber profile: one member per profile row, in
 * `FiberOp.index` order (`ForkFlow.lean:110-124`). `A` and `E` are both
 * `number` here, as they are in every other traced family of this harness. */
export interface FibersService {
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
}

/** Service `Fibers`: one method per operation of the fiber profile. */
export class Fibers extends Context.Service<Fibers, FibersService>()("Fibers") {}

/** Operation rows of `Fibers`, for the trace harness. The spellings are S3's
 * table: `H = Fiber.Fiber<number, number>` and `X = Result.Result<number,
 * number>`. `H` is outside `parseSpelling`'s grammar on purpose, so a fiber
 * falls through to `wire`'s handle branch and reaches the wire as its index. */
export const FibersRows = {
  "fork": { params: 4, answer: "Fiber.Fiber<number, number>" },
  "forkScoped": { params: 4, answer: "Fiber.Fiber<number, number>" },
  "join": { params: 1, answer: "number" },
  "awaitFiber": { params: 1, answer: "Result.Result<number, number>" },
  "interruptFiber": { params: 1, answer: "void" },
  "interruptAll": { params: 1, answer: "void" },
  "childrenSnapshot": { params: 0, answer: "ReadonlyArray<Fiber.Fiber<number, number>>" },
  "awaitChildren": { params: 1, answer: "void" },
  "raceAll": { params: 1, answer: "number" },
  "uninterruptibleIn": { params: 2, answer: "number" },
  "interruptibleIn": { params: 2, answer: "number" },
  "yieldNow": { params: 1, answer: "void" }
}

/** The synthetic dispatch base of a declared root (`fork-lowering.md` §(b),
 * `Lowering.rootEntryBase` in `Effect4/Target/TypeScript/Skeleton.lean`). A
 * declared root is named by its **block id**, so the synthetic case is
 * `rootEntryBase + block` and a fork's `root` field is that block id — which
 * is why the L1 lane exports `prog__root3` for the root at block 3. */
export const rootEntryBase = 1000

/**
 * Lowered from the flow `forkFlow` over `Fibers` (dispatch form, multi-root).
 *
 * Four declared roots at blocks 0, 3, 5 and 7. Block 0 is the entry; block 3
 * answers its argument; block 5 fails with it; block 7 never settles, which is
 * what makes an empty race and a masked child observable.
 */
export const fibersEntry = (
  entry: readonly [number, ReadonlyArray<unknown>]
): Effect.Effect<number, number, Fibers> =>
  Effect.gen(function*() {
    const fibers = yield* Fibers
    let b0p0!: number
    let b1p0!: Fiber.Fiber<number, number>
    let b3p0!: number
    let b5p0!: number
    let b7p0!: number
    let block = entry[0]
    while (true) {
      switch (block) {
        // synthetic root-entry cases, one per declared root
        case 1000: { b0p0 = entry[1][0] as number; block = 0; continue }
        case 1003: { b3p0 = entry[1][0] as number; block = 3; continue }
        case 1005: { b5p0 = entry[1][0] as number; block = 5; continue }
        case 1007: { b7p0 = entry[1][0] as number; block = 7; continue }
        // the flow's own block cases
        case 0: {
          const a0 = yield* fibers.fork(3, [b0p0], false, Option.none<number>())
          b1p0 = a0
          block = 1
          continue
        }
        case 1: {
          const a1 = yield* fibers.join(b1p0)
          return a1
        }
        case 3: return b3p0
        case 5: return yield* Effect.fail(b5p0)
        case 7: return yield* (Effect.never as Effect.Effect<number, number>)
        default: return yield* Effect.die(new Error(`no block ${block}`))
      }
    }
  })

/**
 * The root table: one entry function per declared root, keyed by the root's
 * **block id**, which is what a fork's `root` field carries. The generated
 * fixture spells the same table as one exported function per root
 * (`prog`, `prog__root3`, …) plus the parameterised `progEntry`; collecting
 * them here is what lets the tail resolve a fork without a closure, and what
 * lets it refuse a request naming an undeclared root.
 */
export const fibersRoots: ReadonlyMap<
  number,
  (args: ReadonlyArray<unknown>) => Effect.Effect<number, number, Fibers>
> = new Map([
  [0, (args: ReadonlyArray<unknown>) => fibersEntry([rootEntryBase + 0, args])],
  [3, (args: ReadonlyArray<unknown>) => fibersEntry([rootEntryBase + 3, args])],
  [5, (args: ReadonlyArray<unknown>) => fibersEntry([rootEntryBase + 5, args])],
  [7, (args: ReadonlyArray<unknown>) => fibersEntry([rootEntryBase + 7, args])]
])

/** Lowered from `fiberForkJoin` over `Fibers`: the entry root, by name. */
export const fiberForkJoin = (n: number) => fibersEntry([rootEntryBase + 0, [n]])

/** Lowered from `fiberForkScopedAwait` over `Fibers`. */
export const fiberForkScopedAwait = (n: number) =>
  Effect.gen(function*() {
    const fibers = yield* Fibers
    const a = yield* fibers.forkScoped(3, [n], false, Option.none<number>())
    const x = yield* fibers.awaitFiber(a)
    return x
  })

/** Lowered from `fiberForkInRegion` over `Fibers`. */
export const fiberForkInRegion = (n: number) =>
  Effect.gen(function*() {
    const fibers = yield* Fibers
    const a = yield* fibers.fork(3, [n], false, Option.some(0))
    const y = yield* fibers.join(a)
    return y
  })

/** Lowered from `fiberDaemonSurvives` over `Fibers`. */
export const fiberDaemonSurvives = (n: number) =>
  Effect.gen(function*() {
    const fibers = yield* Fibers
    const a = yield* fibers.fork(3, [n], true, Option.none<number>())
    const x = yield* fibers.awaitFiber(a)
    return x
  })

/** Lowered from `fiberChildrenRoundTrip` over `Fibers`: the tracked set is
 * empty, gains the forked child, and is empty again once that child exits and
 * its observer untracks it (`internal/effect.ts:5281`). The child is root 3,
 * which never settles, so it is still tracked when the middle snapshot is
 * taken. */
export const fiberChildrenRoundTrip = (n: number) =>
  Effect.gen(function*() {
    const fibers = yield* Fibers
    const before = yield* fibers.childrenSnapshot
    yield* fibers.fork(7, [n], false, Option.none<number>())
    const during = yield* fibers.childrenSnapshot
    yield* fibers.interruptAll(during)
    yield* fibers.awaitChildren(before)
    const after = yield* fibers.childrenSnapshot
    return after
  })

/** Lowered from `fiberEmptyRace` over `Fibers`: `Effect.raceAll` over an empty
 * entrant list resumes nobody (`internal/effect.ts:1493-1495`, `len === 0`),
 * so the run parks and the golden is a frontier. */
export const fiberEmptyRace = (n: number) =>
  Effect.gen(function*() {
    const fibers = yield* Fibers
    yield* fibers.yieldNow(n % 2)
    const r = yield* fibers.raceAll([])
    return r
  })

/** Lowered from `fiberInterruptAllChildren` over `Fibers`. */
export const fiberInterruptAllChildren = (n: number) =>
  Effect.gen(function*() {
    const fibers = yield* Fibers
    const a = yield* fibers.fork(7, [n], false, Option.none<number>())
    const b = yield* fibers.fork(7, [n], false, Option.none<number>())
    yield* fibers.interruptFiber(a)
    yield* fibers.interruptAll([a, b])
    const x = yield* fibers.awaitFiber(b)
    return x
  })

/** Lowered from `fiberRaceAllRoots` over `Fibers`. */
export const fiberRaceAllRoots = (n: number) =>
  Effect.gen(function*() {
    const fibers = yield* Fibers
    const r = yield* fibers.raceAll([[3, [n]], [7, [n]]])
    return r
  })

/** Lowered from `fiberMaskedRoot` over `Fibers`. */
export const fiberMaskedRoot = (n: number) =>
  Effect.gen(function*() {
    const fibers = yield* Fibers
    yield* fibers.yieldNow(0)
    const a = yield* fibers.uninterruptibleIn(3, [n])
    const b = yield* fibers.interruptibleIn(3, [a])
    return b
  })
