// STUB: replaced by the generated fixture
/**
 * Hand-typed stand-in for the *full-surface* `Scopes` fixture the L1/L3 lanes
 * generate. The four-row `Scopes` of `scope-fixture.ts` stays exactly as it is
 * — its goldens are pinned — and this declares the rest of rc.112's public
 * `Scope` surface plus the two fiber-linkage sites
 * (`docs/research/2026-09-03-deep-state-models.md` §1.4, §2.4).
 *
 * `strategy` is a boolean rather than a string because the wire alphabet has
 * no string arm for it: `false` is `"sequential"`, rc.112's default
 * (`internal/effect.ts:3915`), and `true` is `"parallel"`. The two strategies
 * differ only in *how* `scopeCloseFinalizers` runs the finalizers
 * (`:3806-3827`): sequentially through `exit()`, or as immediate daemon forks
 * that inherit the closing fiber's mask and are awaited together.
 *
 * `extend` and `use` take a **declared root** the way a fork does, because
 * their argument is a program requiring `Scope` and a request cannot carry
 * one. rc.112 has no `Scope.extend` at this pin: v4's name for "provide the
 * scope without closing it" is `Scope.provide` (`Scope.ts:310-387`).
 */
import { Context, Effect } from "effect"
import type { Fiber, Scope } from "effect"

export interface ScopesFullService {
  readonly make: (parallel: boolean) => Effect.Effect<Scope.Closeable>
  readonly makeUnsafe: (parallel: boolean) => Effect.Effect<Scope.Closeable>
  readonly fork: (
    scope: Scope.Closeable,
    parallel: boolean
  ) => Effect.Effect<Scope.Closeable>
  readonly forkUnsafe: (
    scope: Scope.Closeable,
    parallel: boolean
  ) => Effect.Effect<Scope.Closeable>
  readonly addFinalizer: (scope: Scope.Closeable, key: number) => Effect.Effect<boolean>
  readonly addFinalizerExit: (
    scope: Scope.Closeable,
    key: number
  ) => Effect.Effect<boolean>
  readonly close: (scope: Scope.Closeable) => Effect.Effect<ReadonlyArray<number>>
  readonly extend: (root: number, scope: Scope.Closeable) => Effect.Effect<number>
  readonly use: (root: number, scope: Scope.Closeable) => Effect.Effect<number>
  readonly forkFiberIn: (
    root: number,
    scope: Scope.Closeable
  ) => Effect.Effect<Fiber.Fiber<number, number>>
  readonly runIn: (
    fiber: Fiber.Fiber<number, number>,
    scope: Scope.Closeable
  ) => Effect.Effect<Fiber.Fiber<number, number>>
  /** Which exit each `addFinalizerExit` finalizer observed: `true` for a
   * success exit, `false` otherwise, oldest first. */
  readonly exitsSeen: Effect.Effect<ReadonlyArray<boolean>>
}

export class ScopesFull extends Context.Service<ScopesFull, ScopesFullService>()("ScopesFull") {}

/** Operation rows of `ScopesFull`, for the trace harness. */
export const ScopesFullRows = {
  "make": { params: 1, answer: "Scope.Closeable" },
  "makeUnsafe": { params: 1, answer: "Scope.Closeable" },
  "fork": { params: 2, answer: "Scope.Closeable" },
  "forkUnsafe": { params: 2, answer: "Scope.Closeable" },
  "addFinalizer": { params: 2, answer: "boolean" },
  "addFinalizerExit": { params: 2, answer: "boolean" },
  "close": { params: 1, answer: "ReadonlyArray<number>" },
  "extend": { params: 2, answer: "number" },
  "use": { params: 2, answer: "number" },
  "forkFiberIn": { params: 2, answer: "Fiber.Fiber<number, number>" },
  "runIn": { params: 2, answer: "Fiber.Fiber<number, number>" },
  "exitsSeen": { params: 0, answer: "ReadonlyArray<boolean>" }
}

/** Lowered from `scopeForkLinkage` over `ScopesFull`: a child scope of an open
 * parent, closed from the parent. */
export const scopeForkLinkage = (n: number) =>
  Effect.gen(function*() {
    const scopes = yield* ScopesFull
    const parent = yield* scopes.make(false)
    const child = yield* scopes.fork(parent, false)
    yield* scopes.addFinalizerExit(child, n)
    yield* scopes.addFinalizerExit(parent, n + 1)
    const ran = yield* scopes.close(parent)
    return ran
  })

/** Lowered from `scopeParallelStrategy` over `ScopesFull`. */
export const scopeParallelStrategy = (n: number) =>
  Effect.gen(function*() {
    const scopes = yield* ScopesFull
    const s = yield* scopes.make(true)
    yield* scopes.addFinalizerExit(s, n)
    yield* scopes.addFinalizerExit(s, n + 1)
    const ran = yield* scopes.close(s)
    const seen = yield* scopes.exitsSeen
    return [ran, seen] as const
  })

/** Lowered from `scopeExtendKeepsOpen` over `ScopesFull`: `extend` provides
 * the scope and leaves it open; `use` provides it and closes it with the
 * body's exit. */
export const scopeExtendKeepsOpen = (n: number) =>
  Effect.gen(function*() {
    const scopes = yield* ScopesFull
    const a = yield* scopes.makeUnsafe(false)
    const first = yield* scopes.extend(0, a)
    const stillOpen = yield* scopes.exitsSeen
    yield* scopes.close(a)
    const afterExtend = yield* scopes.exitsSeen
    const b = yield* scopes.makeUnsafe(false)
    const second = yield* scopes.use(0, b)
    const afterUse = yield* scopes.exitsSeen
    return [first, stillOpen, afterExtend, second, afterUse, n] as const
  })

/** Lowered from `scopeFiberLinkage` over `ScopesFull`: `forkIn` registers an
 * interrupt finalizer under a fresh key and an observer that removes it, and
 * `Fiber.runIn` is the same shape without the self-interrupt guard. */
export const scopeFiberLinkage = (n: number) =>
  Effect.gen(function*() {
    const scopes = yield* ScopesFull
    const s = yield* scopes.makeUnsafe(false)
    const f = yield* scopes.forkFiberIn(1, s)
    const g = yield* scopes.runIn(f, s)
    const ran = yield* scopes.close(s)
    return [g, ran, n] as const
  })
