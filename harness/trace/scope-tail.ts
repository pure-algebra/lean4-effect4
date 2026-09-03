import { Effect, Exit, Scope } from "effect"
import {
  Scopes,
  ScopesRows,
  scopeAddAfterClosed,
  scopeCloseTwice,
  scopeLifo,
  scopeRemove
} from "./scope-fixture.ts"
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
registerHandle((value) => ScopeTypeId in value)

type Finalizer = (exit: Exit.Exit<unknown, unknown>) => Effect.Effect<void>

/** Every key this scope's finalizers have run, oldest first. */
const runLog = new WeakMap<Scope.Scope, Array<number>>()
/** The finalizer registered under each key, so `remove` can find it again. */
const registered = new WeakMap<Scope.Scope, Map<number, Finalizer>>()

const name = process.env.EFFECT4_PROGRAM ?? "lifo"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
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

const scopeProgram = (body: (n: number) => Effect.Effect<unknown, never, Scopes>) =>
  Effect.gen(function* () {
    const service = traceService(ScopesRows, live, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(0).pipe(Effect.provideService(Scopes, service))
  })

const programs: Record<string, Effect.Effect<unknown, never, never>> = {
  lifo: scopeProgram(scopeLifo),
  addAfterClosed: scopeProgram(scopeAddAfterClosed),
  remove: scopeProgram(scopeRemove),
  closeTwice: scopeProgram(scopeCloseTwice)
}
const program = programs[name]
if (program === undefined) throw new Error(`unknown program ${name}`)

const report = await runTraced(program, sink, { budget, maxOpsBeforeYield })
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
