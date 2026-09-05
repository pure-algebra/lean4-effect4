// The rc.112 reference for the avatar's `extra` family: the five `WithFiberAction` arms no
// committed golden reaches. Round three of spike A0.
//
// This is NOT a copy of `git:606918eb73daefcc235a261fce879bf910f2471e:harness/trace/fibers-tail.ts` and does not import it: it is a
// standalone mirror that emits the same row alphabet (`Effects/Trace.lean`,
// `git:c407ab7:harness/trace/tracer.ts`), so the avatar has a reference for arms the estate has no
// golden for. It imports `effect` at the estate's pin by absolute path and touches nothing
// under `harness/` or `scripts/`.
//
// There is no decision tape: the handover is an explicit `yield` service row, which both
// faces spell as one primitive (`Effect.yieldNow`, `internal/effect.ts:982-994`). The
// `decide` rows are all `false`, so the two faces' row streams line up.
import * as process from "node:process"
const nm = process.env.EFFECT4_NODE_MODULES ??
  `${process.env.HOME}/Dev/foldlab/library/effects/node_modules`
const { Deferred, Effect, Exit, Fiber } = await import(`${nm}/effect/dist/index.js`)

// ---------------------------------------------------------------- the wire
const handles = new WeakMap()
let nextHandle = 0
const handleIndex = (o) => {
  const seen = handles.get(o)
  if (seen !== undefined) return seen
  const fresh = nextHandle++
  handles.set(o, fresh)
  return fresh
}
const nat = (n) => String(n)
const list = (xs) => xs.reduceRight((acc, x) => `[${x}, ${acc}]`, "[]")
const pair = (a, b) => `[${a}, ${b}]`
const rows = []
const op = (name, request) => rows.push(`op\t${name}\t${request}`)
const answer = (name, value) => rows.push(`answer\t${name}\t${value}`)
const decide = (site, branch) => rows.push(`decide\t${site}\t${branch}`)

const outcomeWire = (exit) => {
  if (exit._tag === "Success") return `{"success":${exit.value}}`
  const reasons = exit.cause?.reasons ?? []
  const fail = reasons.find((r) => r._tag === "Fail")
  if (fail !== undefined) return `{"failure":${fail.error}}`
  if (reasons.some((r) => r._tag === "Interrupt")) return `{"interrupted":true}`
  const die = reasons.find((r) => r._tag === "Die")
  if (die !== undefined) return `{"defect":${JSON.stringify(String(die.defect))}}`
  throw new Error("no Fail, Die or Interrupt reason")
}

// ------------------------------------------------------------ the body table
const started = []
const cleanups = []
const shared = { deferred: null }
const body = (code) => {
  let core
  if (code === 0) core = Effect.succeed(11)
  else if (code === 1) core = Effect.succeed(22)
  else if (code === 5) {
    core = Effect.flatMap(
      // The mask: `Effect.uninterruptible` across the yield, so an interrupt recorded while
      // the child is parked is delivered only when interruptibility is restored (M2).
      Effect.uninterruptible(
        Effect.flatMap(Effect.yieldNow, () => Effect.sync(() => { started.push(6) }))),
      () => Effect.never)
  } else if (code === 6) {
    // Completes the Deferred the program made before forking (M1), through the traced
    // service surface so the row streams are comparable.
    core = Effect.flatMap(
      Effect.suspend(() => {
        op("succeed", pair(nat(handleIndex(shared.deferred)), nat(42)))
        return Effect.tap(Deferred.succeed(shared.deferred, 42),
          (ok) => Effect.sync(() => answer("succeed", String(ok))))
      }),
      () => Effect.succeed(0))
  } else core = Effect.never
  return Effect.onExit(
    Effect.flatMap(Effect.sync(() => { started.push(code) }), () => core),
    () => Effect.sync(() => { cleanups.push(code) }))
}

// ------------------------------------------------------------- the service
let site = 0
const fork = (code) =>
  Effect.gen(function* () {
    op("fork", nat(code))
    const fiber = yield* Effect.forkChild(body(code), { startImmediately: false })
    decide(site++, "false")
    const h = handleIndex(fiber)
    answer("fork", nat(h))
    return fiber
  })
const yieldOp = Effect.gen(function* () {
  op("yield", "[]")
  yield* Effect.yieldNow
  answer("yield", "[]")
})
const awaitAll = (fibers) =>
  Effect.gen(function* () {
    op("awaitAll", list(fibers.map((f) => nat(handleIndex(f)))))
    const exits = yield* Fiber.awaitAll(fibers)
    const values = exits.map((e) => (Exit.isSuccess(e) ? nat(e.value) : "{\"none\":true}"))
    answer("awaitAll", list(values))
    return list(values)
  })
const interruptAll = (fibers) =>
  Effect.gen(function* () {
    op("interruptAll", list(fibers.map((f) => nat(handleIndex(f)))))
    yield* Fiber.interruptAll(fibers)
    answer("interruptAll", "[]")
  })
const readStarted = Effect.gen(function* () {
  op("started", "[]")
  const v = list(started.map(nat))
  answer("started", v)
  return v
})
const readCleanups = Effect.gen(function* () {
  op("cleanups", "[]")
  const v = list(cleanups.map(nat))
  answer("cleanups", v)
  return v
})

// ------------------------------------------------------------- the programs
const programs = {
  awaitAllTwo: Effect.gen(function* () {
    const a = yield* fork(0)
    const b = yield* fork(1)
    return yield* awaitAll([a, b])
  }),
  interruptAllTwo: Effect.gen(function* () {
    const a = yield* fork(4)
    const b = yield* fork(4)
    yield* yieldOp
    const s = yield* readStarted
    yield* interruptAll([a, b])
    yield* readCleanups
    return s
  }),
  siblingCompletesDeferred: Effect.gen(function* () {
    op("make", "[]")
    const d = yield* Deferred.make()
    shared.deferred = d
    answer("make", nat(handleIndex(d)))
    yield* fork(6)
    op("awaitValue", nat(handleIndex(d)))
    const v = yield* Deferred.await(d)
    answer("awaitValue", nat(v))
    return nat(v)
  }),
  maskedYieldKeepsRunning: Effect.gen(function* () {
    const a = yield* fork(5)
    yield* yieldOp
    yield* interruptAll([a])
    const s = yield* readStarted
    yield* readCleanups
    return s
  })
  // `snapshotAwaitNewChildren` and `refusesUnimplementedArm` have no rc.112 surface: the
  // first is fused into `Effect.awaitAllChildren` (the REFUSAL `fibers-tail.ts:33-35`
  // records), the second is a refusal by construction.
}

const name = process.env.EFFECT4_PROGRAM
const program = programs[name]
if (program === undefined) {
  process.stderr.write(`no rc.112 surface for ${name}\n`)
  process.exit(2)
}
const exit = await Effect.runPromiseExit(program)
rows.push(`done\t${outcomeWire(exit)}`)
console.log("format\teffect4-trace-v1")
console.log("face\trc112")
console.log(`program\textra.${name}`)
for (const row of rows) console.log(row)
