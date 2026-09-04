import { Context, Effect, Option } from "effect"
import {
  Contexts,
  ContextsRows,
  contextBuildAndRead,
  contextMergeIsRightBiased,
  contextPickAndOmit,
  contextProvideAndUpdate,
  contextReferenceDefault,
  type ContextsService
} from "./context-fixture.stub.ts"
import { registerHandle, runTraced, traceService, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/**
 * The host face of the `Contexts` family: rc.112's own `Context`, wrapped so
 * the shared alphabet can see it.
 *
 * A `Context` is a `ReadonlyMap<string, unknown>` behind one field
 * (`Context.ts:730`, `makeUnsafe`), and every operation below is that module's
 * own call, cited by line. Nothing here keeps a store: the tail holds only the
 * **key table** the wire indexes into, because a tag is not a wireable value.
 *
 * Three facts of rc.112 the rows are chosen to show:
 *
 * - `merge` and `mergeAll` copy the *later* map over the earlier one
 *   (`:1816-1820`, `:1861-1871`), so a key in both answers the later service.
 * - `get` on an absent `Service` key **throws** — `getUnsafe` (`:1475-1484`)
 *   raises `serviceNotFoundError` (`:1590`) rather than failing typed. That is
 *   the same host-lookup failure the census records for
 *   `layer.build-uses-ambient-scope` (`Layer.ts:800-809`), and here it reaches
 *   the trace as a defect.
 * - a `Context.Reference` (`:2002-2009`) is exempt from that: both `get`
 *   (`:1481`) and `getOption` (`:1708`) fall back to `getDefaultValue`
 *   (`:1582-1588`), which evaluates `defaultValue()` once and caches it on the
 *   reference object itself.
 *
 * A context never reaches the wire as an object: `registerHandle` brands it
 * and `wire` encodes it as its index in first-seen order.
 */

// The brand rc.112 stamps on every context (`Context.ts:587` TypeId). It is a
// string key, not an exported value, so it is written out here. A tag carries
// `~effect/Context/Service` (`:41`) instead, so tags are not branded as
// contexts.
const ContextTypeId = "~effect/Context"
registerHandle((value) => ContextTypeId in value)

const name = process.env.EFFECT4_PROGRAM ?? "buildAndRead"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const sink: Event[] = []

/** Three declared service tags and one reference, all carrying a number. */
class K0 extends Context.Service<K0, number>()("K0") {}
class K1 extends Context.Service<K1, number>()("K1") {}
class K2 extends Context.Service<K2, number>()("K2") {}
/** `Context.Reference` — `Context.ts:2002-2009`; `defaultValue` is evaluated
 * at most once and cached on the reference (`getDefaultValue`, `:1582-1588`). */
let defaultEvaluations = 0
const K3 = Context.Reference<number>("K3", {
  defaultValue: () => {
    defaultEvaluations += 1
    return 41
  }
})

/** The key table the wire indexes into. The cast is the wire's untyped `Val`
 * surfacing on the host: a request names a key by index and cannot carry the
 * key's identifier type, which is the same refusal `fork-lowering.md` §(b)
 * records for `entry[1]`. */
const keys = [K0, K1, K2, K3] as unknown as ReadonlyArray<Context.Key<never, number>>

const keyAt = (index: number): Context.Key<never, number> | undefined => keys[index]

const missingKey = (op: string, index: number): Effect.Effect<never> =>
  Effect.die(new Error(`${op}: the request names no declared key ${index}`))

/** Declared roots, the way a fork names one: a program reading a service out
 * of its own context. Root 0 reads key 0, which is what makes `provide` and
 * `updateContext` observable. */
const contextRoots: ReadonlyArray<Effect.Effect<number, never, K0>> = [
  Effect.gen(function* () {
    const value = yield* K0
    return value
  })
]

const live: ContextsService = {
  // `Context.empty` — `Context.ts:853`: the one shared empty context.
  empty: Effect.sync(() => Context.empty()),
  // `Context.make` — `Context.ts:874-877`: a context over a one-entry `Map`
  // keyed on `key.key`, the tag's *string*.
  make: (key, value) => {
    const tag = keyAt(key)
    if (tag === undefined) return missingKey("make", key)
    return Effect.sync(() => Context.make(tag, value) as Context.Context<never>)
  },
  // `Context.add` — `Context.ts:915`, impl `:990-994` over `addUnsafe`
  // (`:1002`): a fresh flat map with the entry set, so the argument context is
  // never mutated.
  add: (context, key, value) => {
    const tag = keyAt(key)
    if (tag === undefined) return missingKey("add", key)
    return Effect.sync(() => Context.add(context, tag, value) as Context.Context<never>)
  },
  // `Context.get` — `Context.ts:1517`, impl `:1580` (`= getUnsafe`), whose
  // body is `:1475-1484`: a missing `Service` key **throws**
  // `serviceNotFoundError`; a missing `Reference` answers its cached default.
  // The throw crosses the tracer as a defect, which is the honest reading —
  // rc.112 does not make this a typed failure.
  get: (context, key) => {
    const tag = keyAt(key)
    if (tag === undefined) return missingKey("get", key)
    return Effect.sync(() => Context.get(context, tag))
  },
  // `Context.getOption` — `Context.ts:1636`, impl `:1705-1709`: `Some` on a
  // hit, `Some` of the default for a `Reference`, `None` otherwise.
  getOption: (context, key) => {
    const tag = keyAt(key)
    if (tag === undefined) return missingKey("getOption", key)
    return Effect.sync(() => Context.getOption(context, tag))
  },
  // `Context.merge` — `Context.ts:1745`, impl `:1816-1820`: `that`'s entries
  // are set over a flat copy of `self`, so `that` wins on a shared key; an
  // empty side is returned as-is rather than copied.
  merge: (self, that) => Effect.sync(() => Context.merge(self, that) as Context.Context<never>),
  // `Context.mergeAll` — `Context.ts:1861-1871`: one fresh `Map`, every
  // argument's entries set into it in order, so the last argument wins. Unlike
  // `merge` it never answers an argument itself, even for a single or an empty
  // argument list. The list arrives as the `twoContexts` atom's answer.
  mergeAll: (contexts) =>
    Effect.sync(() => Context.mergeAll(...contexts) as Context.Context<never>),
  // `Context.pick` — `Context.ts:1904-1913`: a flat copy with every key not in
  // the kept set deleted.
  pick: (context, key) => {
    const tag = keyAt(key)
    if (tag === undefined) return missingKey("pick", key)
    return Effect.sync(() => Context.pick(tag)(context) as Context.Context<never>)
  },
  // `Context.omit` — `Context.ts:1946-1954`: a flat copy with the named keys
  // deleted.
  omit: (context, key) => {
    const tag = keyAt(key)
    if (tag === undefined) return missingKey("omit", key)
    return Effect.sync(() => Context.omit(tag)(context) as Context.Context<never>)
  },
  // `Effect.provideContext` — `Effect.ts:11667` =
  // `internal/effect.ts:2180-2199`: an `Exit` is returned unchanged, and
  // everything else is `updateContext(self, Context.merge(context))`, so the
  // provided context is merged *under* the fiber's own.
  provide: (root, context) => {
    const body = contextRoots[root]
    if (body === undefined) {
      return Effect.die(new Error(`provide: the request names no declared root ${root}`))
    }
    return Effect.provideContext(body, context as Context.Context<K0>)
  },
  // `Effect.updateContext` — `Effect.ts:12004` =
  // `internal/effect.ts:2073-2097`: reads the running fiber's context, applies
  // the function, and short-circuits when the function returns the same object.
  updateContext: (root, key, value) => {
    const body = contextRoots[root]
    const tag = keyAt(key)
    if (body === undefined) {
      return Effect.die(new Error(`updateContext: the request names no declared root ${root}`))
    }
    if (tag === undefined) return missingKey("updateContext", key)
    return Effect.updateContext(
      body,
      (context: Context.Context<never>) =>
        Context.add(context, tag, value) as unknown as Context.Context<K0>
    )
  },
  // rc.112 has no `Effect.withContext` at this pin: the reader is
  // `Effect.contextWith` (`Effect.ts:11346` = `internal/effect.ts:2156-2158`),
  // `withFiber(fiber => f(fiber.context))`, and `Effect.context()` (`:2152`)
  // is the same read as a value. The answer is which declared keys the running
  // fiber's own context carries.
  withContext: Effect.contextWith((context: Context.Context<never>) =>
    Effect.succeed(
      keys.flatMap((tag, index) => (Option.isSome(Context.getOption(context, tag)) ? [index] : []))
    )
  ),
  // How many times `K3`'s `defaultValue` thunk has actually run. rc.112 caches
  // it on the reference object under `~effect/Context/defaultValue`
  // (`Context.ts:1582-1588`), so this stays at one however often the reference
  // is read from a context that does not carry it.
  referenceDefault: Effect.sync(() => defaultEvaluations)
}

const contextProgram = (body: (n: number) => Effect.Effect<unknown, never, Contexts>) =>
  Effect.gen(function* () {
    const service = traceService(ContextsRows, live, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(7).pipe(Effect.provideService(Contexts, service))
  })

const programs: Record<string, Effect.Effect<unknown, never, never>> = {
  buildAndRead: contextProgram(contextBuildAndRead),
  mergeIsRightBiased: contextProgram(contextMergeIsRightBiased),
  pickAndOmit: contextProgram(contextPickAndOmit),
  provideAndUpdate: contextProgram(contextProvideAndUpdate),
  referenceDefault: contextProgram(contextReferenceDefault)
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
