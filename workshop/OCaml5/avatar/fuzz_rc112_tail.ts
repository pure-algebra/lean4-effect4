/**
 * The rc.112 face of P5's generated corpus (`workshop/OCaml5/fuzz/corpus/corpus-fixture.ts`,
 * spike P5 round four). Round five of spike A0.
 *
 * P5 renders each random program to both an OCaml fixture and this TypeScript one; the OCaml
 * half is compiled into the avatar as the `fuzz` family, and this tail runs the TypeScript
 * half over the pinned rc.112. It imports P5's fixture and nothing from `harness/`: the wire,
 * the first-seen handle counter, the tape and the stall deadline are transcribed here, so the
 * two faces stay independent implementations of one generated program.
 */
import { Context, Deferred, Effect, Exit, Fiber, Layer, Ref, Scope, Scheduler } from "effect"
import * as Corpus from "./corpus-fixture.ts"

declare const process: { readonly env: Record<string, string | undefined> }

const rows: string[] = []
const handles = new WeakMap<object, number>()
let nextHandle = 0
const handleIndex = (o: object): number => {
  const seen = handles.get(o)
  if (seen !== undefined) return seen
  const fresh = nextHandle++
  handles.set(o, fresh)
  return fresh
}
const brands = ["~effect/Fiber", "~effect/Ref", "~effect/Scope", "~effect/Deferred"]
const isHandle = (v: object): boolean => brands.some((b) => b in (v as Record<string, unknown>))

const wire = (v: unknown): string => {
  if (v === undefined || v === null) return "[]"
  if (typeof v === "number") return String(v)
  if (typeof v === "boolean") return v ? "true" : "false"
  if (typeof v === "string") return JSON.stringify(v)
  if (Array.isArray(v)) return v.reduceRight<string>((acc, x) => `[${wire(x)}, ${acc}]`, "[]")
  if (typeof v === "object") {
    const tag = (v as { _tag?: string })._tag
    if (tag === "Some") return `{"some":${wire((v as { value: unknown }).value)}}`
    if (tag === "None") return `{"none":true}`
    if (tag === "Success") return `[true, ${wire((v as { success: unknown }).success)}]`
    if (tag === "Failure") return `[false, ${wire((v as { failure: unknown }).failure)}]`
    if (isHandle(v as object)) return String(handleIndex(v as object))
  }
  return String(v)
}
const wireArgs = (args: ReadonlyArray<unknown>): string => {
  if (args.length === 0) return "[]"
  if (args.length === 1) return wire(args[0])
  return args.slice(0, -1).reduceRight<string>((acc, x) => `[${wire(x)}, ${acc}]`, wire(args[args.length - 1]))
}

/** The estate's `traceService`, transcribed: `op` at the call, `answer` when the effect
 * completes, `failed` when it fails. */
const traceService = <S extends object>(spec: Record<string, { params: number }>, impl: S): S => {
  const out: Record<string, unknown> = {}
  for (const [name, row] of Object.entries(spec)) {
    const method = (impl as Record<string, unknown>)[name]
    const around = (args: ReadonlyArray<unknown>, effect: Effect.Effect<unknown, unknown, unknown>) =>
      Effect.suspend(() => {
        rows.push(`op\t${name}\t${wireArgs(args)}`)
        return effect.pipe(
          Effect.tap((v) => Effect.sync(() => { rows.push(`answer\t${name}\t${wire(v)}`) })),
          Effect.tapError((e) => Effect.sync(() => { rows.push(`failed\t${name}\t${wire(e)}`) }))
        )
      })
    out[name] = row.params === 0
      ? around([], method as Effect.Effect<unknown, unknown, unknown>)
      : (...args: unknown[]) => around(args, (method as (...a: unknown[]) => Effect.Effect<unknown, unknown, unknown>)(...args))
  }
  return out as S
}

// ------------------------------------------------------------------- the tape
const tape: Array<readonly [number, boolean]> = (process.env.EFFECT4_TAPE ?? "")
  .split(",").filter((e) => e.length > 0)
  .map((e) => { const [s, b] = e.split(":"); return [Number(s), b === "1"] as const })
let cursor = 0
let armed = false
const decide = (): boolean => {
  const e = tape[cursor]
  if (e === undefined) throw new Error(`TAPE_EXHAUSTED at ${cursor}`)
  cursor += 1
  rows.push(`decide\t${e[0]}\t${e[1] ? "true" : "false"}`)
  return e[1]
}
class TapeScheduler extends Scheduler.MixedScheduler {
  override shouldYield(fiber: any): boolean {
    if (armed) { armed = false; return true }
    return super.shouldYield(fiber)
  }
}

// ------------------------------------------------------------ the live services
const started: number[] = []
const cleanups: number[] = []
const body = (code: number): Effect.Effect<number, number> => {
  const core: Effect.Effect<number, number> =
    code === 0 ? Effect.succeed(11) : code === 1 ? Effect.succeed(22)
    : code === 2 ? (Effect.fail(1) as Effect.Effect<number, number>)
    : code === 3 ? (Effect.fail(2) as Effect.Effect<number, number>)
    : (Effect.never as unknown as Effect.Effect<number, number>)
  return Effect.onExit(
    Effect.flatMap(Effect.sync(() => { started.push(code) }), () => core),
    () => Effect.sync(() => { cleanups.push(code) }))
}
const forkWith = (fork: Effect.Effect<Fiber.Fiber<number, number>>) =>
  Effect.gen(function* () {
    const fiber = yield* fork
    if (decide()) { armed = true; yield* Effect.sync(() => {}) }
    return fiber
  })

class L0 extends Context.Service<L0, Ref.Ref<number>>()("A0FL0") {}
class L1 extends Context.Service<L1, Ref.Ref<number>>()("A0FL1") {}
class L2 extends Context.Service<L2, Ref.Ref<number>>()("A0FL2") {}
const counts = new Map<number, number>()
const scopeOfService = new WeakMap<Ref.Ref<number>, Scope.Scope>()
const releaseLog: Array<Ref.Ref<number>> = []
const construct = (base: number) =>
  Effect.gen(function* () {
    const layerScope = yield* Effect.scope
    counts.set(base, (counts.get(base) ?? 0) + 1)
    const service = yield* Ref.make(base)
    scopeOfService.set(service, layerScope)
    yield* Scope.addFinalizerExit(layerScope, () => Effect.sync(() => { releaseLog.push(service) }))
    return service
  })
const declared = [
  { layer: Layer.effect(L0, construct(0)), tag: L0 },
  { layer: Layer.effect(L1, construct(1)), tag: L1 },
  { layer: Layer.effect(L2, construct(2)), tag: L2 }
] as any
declared.push({ layer: Layer.fresh(declared[1].layer), tag: L1 })
const memoMap = Layer.makeMemoMapUnsafe()
const layerRoot = Scope.makeUnsafe()
const scopeRunLog = new WeakMap<object, number[]>()
const scopeRegistered = new WeakMap<object, Map<number, any>>()

const liveFibers = {
  fork: (code: number) => forkWith(Effect.forkChild(body(code), { startImmediately: false })),
  forkDetach: (code: number) => forkWith(Effect.forkDetach(body(code), { startImmediately: false })),
  join: (f: any) => Fiber.join(f),
  awaitValue: (f: any) => Effect.map(Fiber.await(f), (e: any) => e._tag === "Success" ? { _tag: "Some", value: e.value } : { _tag: "None" }),
  awaitError: (f: any) => Effect.map(Fiber.await(f), (e: any) => {
    if (e._tag === "Success") return { _tag: "None" }
    const fail = ((e.cause?.reasons ?? []) as any[]).find((r) => r._tag === "Fail")
    return fail === undefined ? { _tag: "None" } : { _tag: "Some", value: fail.error }
  }),
  interrupt: (f: any) => Fiber.interrupt(f),
  started: Effect.sync(() => started.slice()),
  cleanups: Effect.sync(() => cleanups.slice()),
  yieldNow: (_p: number) => Effect.yieldNow,
  interruptAll: (fs: any) => Fiber.interruptAll(fs),
  awaitAll: (fs: any) => Effect.asVoid(Fiber.awaitAll(fs))
}
const liveRefs = {
  make: (n: number) => Ref.make(n), get: (r: any) => Ref.get(r),
  set: (r: any, v: number) => Effect.asVoid(Ref.set(r, v)),
  update: (r: any, a: number) => Ref.update(r, (c: number) => c + a),
  modify: (r: any, a: number) => Ref.modify(r, (c: number) => [c, c + a] as const),
  getAndSet: (r: any, v: number) => Ref.getAndSet(r, v)
}
const liveDeferreds = {
  make: Deferred.make<number, number>(),
  succeed: (d: any, v: number) => Deferred.succeed(d, v),
  fail: (d: any, e: number) => Deferred.fail(d, e),
  isDone: (d: any) => Deferred.isDone(d),
  poll: (d: any) => Effect.map(Deferred.poll(d), (o: any) =>
    o._tag === "None" ? { _tag: "None" }
      : { _tag: "Some", value: o.value._tag === "Success"
          ? { _tag: "Success", success: o.value.value }
          : { _tag: "Failure", failure: ((o.value.cause?.reasons ?? []) as any[]).find((r) => r._tag === "Fail")?.error } }),
  awaitValue: (d: any) => Deferred.await(d),
  awaitError: (d: any) => Effect.flip(Deferred.await(d))
}
const liveScopes = {
  make: Effect.sync(() => {
    const s = Scope.makeUnsafe(); scopeRunLog.set(s, []); scopeRegistered.set(s, new Map()); return s
  }),
  addFinalizer: (s: any, key: number) => Effect.gen(function* () {
    const ran = scopeRunLog.get(s) ?? []; const before = ran.length
    const fin = () => Effect.sync(() => { ran.push(key) })
    scopeRegistered.get(s)?.set(key, fin)
    yield* Scope.addFinalizerExit(s, fin)
    return ran.length === before
  }),
  remove: (s: any, key: number) => Effect.sync(() => {
    const fin = scopeRegistered.get(s)?.get(key); const state = s.state
    if (fin === undefined || state._tag !== "Open") return
    if (state.finalizer === fin) { state.finalizerKey = undefined; state.finalizer = undefined; return }
    const table = state.finalizers; if (table === undefined) return
    for (const [k, e] of table) if (e === fin) { table.delete(k); return }
  }),
  close: (s: any) => Effect.gen(function* () {
    const ran = scopeRunLog.get(s) ?? []; const before = ran.length
    yield* Scope.close(s, Exit.void)
    return ran.slice(before)
  })
}
const liveLayers = {
  build: (k: number) => Effect.gen(function* () {
    const entry = declared[k]
    const context = yield* Layer.buildWithMemoMap(entry.layer, memoMap, layerRoot)
    return Context.get(context, entry.tag)
  }),
  provideCount: (b: number) => Effect.sync(() => counts.get(b) ?? 0),
  scopeOf: (sv: any) => Effect.sync(() => scopeOfService.get(sv) as any),
  close: Effect.gen(function* () {
    const before = releaseLog.length
    yield* Scope.close(layerRoot, Exit.void)
    return releaseLog.slice(before)
  })
}

const outcomeWire = (exit: any): string => {
  if (exit._tag === "Success") return `{"success":${wire(exit.value)}}`
  const reasons = (exit.cause?.reasons ?? []) as any[]
  const fail = reasons.find((r) => r._tag === "Fail")
  if (fail !== undefined) return `{"failure":${wire(fail.error)}}`
  if (reasons.some((r) => r._tag === "Interrupt")) return `{"interrupted":true}`
  const die = reasons.find((r) => r._tag === "Die")
  if (die !== undefined) return `{"defect":${JSON.stringify(String(die.defect))}}`
  throw new Error("no Fail, Die or Interrupt reason")
}

const name = process.env.EFFECT4_PROGRAM ?? "p400000"
const lowered = (Corpus as Record<string, any>)[`corpus_${name}`]
if (lowered === undefined) throw new Error(`unknown corpus program ${name}`)

const program = lowered(0).pipe(
  Effect.provideService(Corpus.Fibers, traceService(Corpus.FibersRows, liveFibers) as any),
  Effect.provideService(Corpus.Refs, traceService(Corpus.RefsRows, liveRefs) as any),
  Effect.provideService(Corpus.Deferreds, traceService(Corpus.DeferredsRows, liveDeferreds) as any),
  Effect.provideService(Corpus.Scopes, traceService(Corpus.ScopesRows, liveScopes) as any),
  Effect.provideService(Corpus.Layers, traceService(Corpus.LayersRows, liveLayers) as any),
  Effect.provideService(Scheduler.MaxOpsBeforeYield, Number(process.env.EFFECT4_MAX_OPS ?? "1000000"))
)
const fiber = Effect.runFork(program as any, { scheduler: new TapeScheduler() })
const settled: Promise<unknown> = new Promise((resolve) => (fiber as any).addObserver(resolve))
const stalled = Symbol("stalled")
const deadline: Promise<unknown> = new Promise((resolve) =>
  setTimeout(() => resolve(stalled), Number(process.env.EFFECT4_STALL_MS ?? "300")))
const first = await Promise.race([settled, deadline])
if (first === stalled) rows.push("frontier")
else rows.push(`done\t${outcomeWire(first)}`)

console.log("format\teffect4-trace-v1")
console.log("face\trc112")
console.log(`program\tfuzz.${name}`)
for (const r of rows) console.log(r)
