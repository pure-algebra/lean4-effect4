import { Effect, Exit, Fiber, Scope } from "effect"
import {
  Scopes,
  ScopesRows,
  scopeAddAfterClosed,
  scopeCloseTwice,
  scopeLifo,
  scopeRemove
} from "./scope-fixture.ts"
import {
  ScopesFull,
  ScopesFullRows,
  scopeExtendKeepsOpen,
  scopeFiberLinkage,
  scopeForkLinkage,
  scopeParallelStrategy,
  type ScopesFullService
} from "./scopes-fixture.stub.ts"
import { registerHandle, runTraced, traceService, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/**
 * The host face of the `Scopes` family: rc.112's own `Scope`, wrapped so the
 * shared alphabet can see it.
 *
 * - `make` is `Scope.makeUnsafe()`, whose default strategy is `"sequential"`.
 * - `addFinalizer` is `Scope.addFinalizerExit`. Its answer is whether the
 *   scope was still open: on a closed scope rc.112 runs the finalizer at once
 *   (`internal/effect.ts` `scopeAddFinalizerExit`), which shows up as the run
 *   log growing during the add.
 * - `close` is `Scope.close(scope, Exit.void)`, and its answer is the slice of
 *   the run log this close appended: the keys rc.112 actually ran, in the order
 *   it ran them. A second close appends nothing and answers `[]`.
 * - `remove` has no rc.112 entry point: the package's exports map
 *   `"./internal/*"` to `null`, so `scopeRemoveFinalizerUnsafe` is unreachable
 *   from here. It is performed over the *public* mutable `Scope.state`
 *   (`Scope.ts` `State.Open`), in the same two arms rc.112's own removal uses —
 *   clear the inline slot, else delete from the map — locating the entry by the
 *   identity of the finalizer registered under that key. The `remove` golden
 *   pins that state shape and the Lean model, not an rc.112 call.
 *
 * A scope never reaches the wire as an object. `registerHandle` brands it and
 * `wire` encodes it as its index in first-seen order, which is the creation
 * order the Lean face numbers scopes in.
 */

// The brand rc.112 stamps on every scope (`internal/effect.ts` ScopeTypeId).
// It is a string key, not an exported value, so it is written out here.
const ScopeTypeId = "~effect/Scope"
// The two fiber-linkage rows (`forkFiberIn`, `runIn`) answer a fiber, so the
// fiber brand (`Fiber.ts:24`) needs a handle carrier here too.
const FiberTypeId = "~effect/Fiber"
registerHandle((value) => ScopeTypeId in value || FiberTypeId in value)

type Finalizer = (exit: Exit.Exit<unknown, unknown>) => Effect.Effect<void>

/** Every key this scope's finalizers have run, oldest first. */
const runLog = new WeakMap<Scope.Scope, Array<number>>()
/** The finalizer registered under each key, so `remove` can find it again. */
const registered = new WeakMap<Scope.Scope, Map<number, Finalizer>>()

const name = process.env.EFFECT4_PROGRAM ?? "lifo"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const stallMs = Number(process.env.EFFECT4_STALL_MS ?? "50")
const sink: Event[] = []

const live = {
  make: Effect.sync(() => {
    const scope = Scope.makeUnsafe()
    runLog.set(scope, [])
    registered.set(scope, new Map())
    return scope
  }),
  addFinalizer: (scope: Scope.Closeable, key: number) =>
    Effect.gen(function* () {
      const ran = runLog.get(scope) ?? []
      const before = ran.length
      const finalizer: Finalizer = () => Effect.sync(() => { ran.push(key) })
      registered.get(scope)?.set(key, finalizer)
      yield* Scope.addFinalizerExit(scope, finalizer)
      // Unchanged means rc.112 stored it; grown means the scope had closed and
      // rc.112 ran it on the spot.
      return ran.length === before
    }),
  remove: (scope: Scope.Closeable, key: number) =>
    Effect.sync(() => {
      const finalizer = registered.get(scope)?.get(key)
      const state = scope.state
      if (finalizer === undefined || state._tag !== "Open") return
      if (state.finalizer === finalizer) {
        state.finalizerKey = undefined
        state.finalizer = undefined
        return
      }
      const table = state.finalizers
      if (table === undefined) return
      for (const [entryKey, entry] of table) {
        if (entry === finalizer) {
          table.delete(entryKey)
          return
        }
      }
    }),
  close: (scope: Scope.Closeable) =>
    Effect.gen(function* () {
      const ran = runLog.get(scope) ?? []
      const before = ran.length
      yield* Scope.close(scope, Exit.void)
      return ran.slice(before)
    })
}

/**
 * The rest of rc.112's public `Scope` surface, plus the two fiber-linkage
 * sites (`docs/research/2026-09-03-deep-state-models.md` §2.4). Every method is
 * an rc.112 call, cited by line; the one operation that has no rc.112 entry
 * point is `remove` above, and that stays exactly as it was.
 */

/** Which exit each `addFinalizerExit` finalizer observed, oldest first. */
const exitsSeen: boolean[] = []

/** A declared root, the way a fork names one: a body requiring `Scope`, which
 * `extend` and `use` supply. Root 0 registers a finalizer on the scope it is
 * given and answers a number; root 1 is a child that never settles, so a
 * scope's interrupt finalizer is observable. */
const scopeRoots: ReadonlyArray<Effect.Effect<number, never, Scope.Scope>> = [
  Effect.gen(function* () {
    const scope = yield* Scope.Scope
    // `Scope.addFinalizerExit` — `Scope.ts:422-423` =
    // `internal/effect.ts:3847-3858`.
    yield* Scope.addFinalizerExit(scope, () => Effect.sync(() => { exitsSeen.push(true) }))
    return 1
  }),
  Effect.succeed(2)
]

const forkBodies: ReadonlyArray<Effect.Effect<number, number>> = [
  Effect.succeed(11),
  Effect.never as unknown as Effect.Effect<number, number>
]

const strategyOf = (parallel: boolean): "sequential" | "parallel" =>
  parallel ? "parallel" : "sequential"

/** Register the run-log finalizer of `key` on `scope` and report whether the
 * scope was still open — the same reading the narrow `addFinalizer` row uses:
 * unchanged means rc.112 stored it, grown means the scope had closed and
 * rc.112 ran it on the spot (`internal/effect.ts:3847-3858`). */
const registerFinalizer = (
  scope: Scope.Closeable,
  key: number,
  observe: boolean
): Effect.Effect<boolean> =>
  Effect.gen(function* () {
    const ran = runLog.get(scope) ?? []
    const before = ran.length
    const finalizer: Finalizer = (exit) =>
      Effect.sync(() => {
        ran.push(key)
        if (observe) exitsSeen.push(exit._tag === "Success")
      })
    registered.get(scope)?.set(key, finalizer)
    yield* Scope.addFinalizerExit(scope, finalizer)
    return ran.length === before
  })

/** Track a scope the harness did not mint through the narrow `make` row, so
 * `close` can still report the slice of the run log it appended. */
const track = (scope: Scope.Closeable): Scope.Closeable => {
  if (!runLog.has(scope)) runLog.set(scope, [])
  if (!registered.has(scope)) registered.set(scope, new Map())
  return scope
}

const fullLive: ScopesFullService = {
  // `Scope.make` — `Scope.ts:240` = `internal/effect.ts:3925-3930`; the
  // strategy defaults to `"sequential"` (`:3915`).
  make: (parallel) => Effect.map(Scope.make(strategyOf(parallel)), track),
  // `Scope.makeUnsafe` — `Scope.ts:271` = `internal/effect.ts:3915-3922`.
  makeUnsafe: (parallel) => Effect.sync(() => track(Scope.makeUnsafe(strategyOf(parallel)))),
  // `Scope.fork` — `Scope.ts:489-492` = `internal/effect.ts:3830-3832` over
  // `scopeForkUnsafe` (`:3834-3844`): a child of a `Closed` parent is born
  // `Closed` with the parent's exit; otherwise one shared key links a parent
  // finalizer closing the child to a child finalizer removing itself from the
  // parent.
  fork: (scope, parallel) => Effect.map(Scope.fork(scope, strategyOf(parallel)), track),
  // `Scope.forkUnsafe` — `Scope.ts:530-531` = `internal/effect.ts:3834-3844`.
  forkUnsafe: (scope, parallel) =>
    Effect.sync(() => track(Scope.forkUnsafe(scope, strategyOf(parallel)))),
  // `Scope.addFinalizer` — `Scope.ts:456`; the exit-blind form.
  addFinalizer: (scope, key) => registerFinalizer(scope, key, false),
  // `Scope.addFinalizerExit` — `Scope.ts:422-423`; the exit-aware form, whose
  // finalizer sees the exit the scope closed with.
  addFinalizerExit: (scope, key) => registerFinalizer(scope, key, true),
  // `Scope.close` — `Scope.ts:567` = `internal/effect.ts:3775-3777` over
  // `scopeCloseUnsafe` (`:3779-3798`) and `scopeCloseFinalizers`
  // (`:3806-3827`). The answer is the slice of the run log this close
  // appended: the keys rc.112 actually ran, in the order it ran them.
  close: (scope) =>
    Effect.gen(function* () {
      const ran = runLog.get(scope) ?? []
      const before = ran.length
      yield* Scope.close(scope, Exit.void)
      return ran.slice(before)
    }),
  // `Scope.provide` — `Scope.ts:310-387` = `internal/effect.ts:3932-3936`
  // (`provideScope`, which is `provideService(scopeTag)`): the scope is put in
  // the body's context and is **not** closed afterwards. rc.112 has no
  // `Scope.extend`; this is the v4 name for it.
  extend: (root, scope) => {
    const body = scopeRoots[root]
    if (body === undefined) {
      return Effect.die(new Error(`extend: the request names no declared root ${root}`))
    }
    return Scope.provide(body, scope)
  },
  // `Scope.use` — `Scope.ts:616-661` = `internal/effect.ts:3950-3959`:
  // `onExit(provideScope(self, scope), exit => scopeCloseUnsafe(scope, exit))`,
  // so the scope is closed with the *same* exit the body produced.
  use: (root, scope) => {
    const body = scopeRoots[root]
    if (body === undefined) {
      return Effect.die(new Error(`use: the request names no declared root ${root}`))
    }
    return Scope.use(body, scope)
  },
  // `Effect.forkIn` — `Effect.ts:17033` = `internal/effect.ts:5337-5379`: a
  // non-exited child registers, under a fresh key, a finalizer that interrupts
  // it unless the interruptor is the child itself, plus an observer that
  // removes that key; a `Closed` scope interrupts the child at once (`:5374`).
  forkFiberIn: (root, scope) => {
    const body = forkBodies[root]
    if (body === undefined) {
      return Effect.die(new Error(`forkFiberIn: the request names no declared root ${root}`))
    }
    return Effect.forkIn(body, scope, { startImmediately: false })
  },
  // `Fiber.runIn` — `Fiber.ts:758-805` = `internal/effect.ts:5441-5461`
  // (`fiberRunIn`): the same shape without the self-interrupt guard. It is not
  // an Effect in rc.112 — it registers and returns the same fiber — so the
  // row's effect is the `sync` around it.
  runIn: (fiber, scope) => Effect.sync(() => Fiber.runIn(fiber, scope)),
  exitsSeen: Effect.sync(() => exitsSeen.slice())
}

const scopeProgram = (body: (n: number) => Effect.Effect<unknown, never, Scopes>) =>
  Effect.gen(function* () {
    const service = traceService(ScopesRows, live, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(0).pipe(Effect.provideService(Scopes, service))
  })

const fullProgram = (body: (n: number) => Effect.Effect<unknown, never, ScopesFull>) =>
  Effect.gen(function* () {
    const service = traceService(ScopesFullRows, fullLive, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(0).pipe(Effect.provideService(ScopesFull, service))
  })

const programs: Record<string, Effect.Effect<unknown, never, never>> = {
  lifo: scopeProgram(scopeLifo),
  addAfterClosed: scopeProgram(scopeAddAfterClosed),
  remove: scopeProgram(scopeRemove),
  closeTwice: scopeProgram(scopeCloseTwice),
  forkLinkage: fullProgram(scopeForkLinkage),
  parallelStrategy: fullProgram(scopeParallelStrategy),
  extendKeepsOpen: fullProgram(scopeExtendKeepsOpen),
  fiberLinkage: fullProgram(scopeFiberLinkage)
}
const program = programs[name]
if (program === undefined) throw new Error(`unknown program ${name}`)

/** A run that parks — a scope holding a child that never settles — evaluates
 * no further primitive, so the op budget cannot fire; the stall deadline turns
 * the park into the frontier the golden records (`RunOptions.stallMs`). */
const stalls = name === "fiberLinkage"

const report = await runTraced(
  program,
  sink,
  stalls ? { budget, maxOpsBeforeYield, stallMs } : { budget, maxOpsBeforeYield }
)
sink.push({ kind: "phase", phase: "teardown" })
console.log(JSON.stringify({
  rows: windowRows(report.events),
  frames: report.frames,
  exitTag: report.exitTag,
  primitives: report.primitives,
  yields: report.yields,
  scheduled: report.scheduled,
  tracerDefect: report.tracerDefect,
  maxOpsBeforeYield,
  expectYields: process.env.EFFECT4_EXPECT_YIELDS === "1",
  foreign: []
}))
