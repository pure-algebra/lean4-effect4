// Pool probes over one Effect 4 build (2026-10-06). Finite host runs, not proofs.
//
// Run: EFFECT_DIR=<an effect package directory> bun run pool-lifecycle.ts
// The package directory is the one that holds package.json and dist/index.js.
// Each probe is one schedule. The output names the build's version and the runtime's.
import { readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const E = await import(`${dir}/dist/index.js`)
const { Effect, Deferred, Pool, Scope, Exit } = E

const fork = Effect.forkChild
const settle = Effect.gen(function*() {
  for (let i = 0; i < 24; i++) yield* Effect.yieldNow
})

// A resource is a number, in the order of its acquisition. The log records each acquisition and
// each finalizer.
const resource = (log: Array<string>, before?: any) => {
  let n = 0
  const acquire = Effect.sync(() => {
    const id = ++n
    log.push(`acquire ${id}`)
    return id
  })
  return Effect.acquireRelease(
    before === undefined ? acquire : Effect.flatMap(before, () => acquire),
    (id: number) => Effect.sync(() => { log.push(`finalize ${id}`) })
  )
}

// A pool inside a scope that the probe closes itself.
const openPool = (options: any) =>
  Effect.gen(function*() {
    const scope = yield* Scope.make()
    const pool: any = yield* Effect.provideService(Pool.make(options), Scope.Scope, scope)
    yield* settle
    return { pool, scope }
  })

// A borrower takes one item inside a scope of its own, and returns it when that scope closes.
// With a gate it holds the item until the gate opens.
const borrower = (pool: any, name: string, log: Array<string>, gate?: any) =>
  fork(Effect.scoped(Effect.gen(function*() {
    const r = yield* Pool.get(pool)
    log.push(`${name} got ${r}`)
    if (gate !== undefined) yield* Deferred.await(gate)
    log.push(`${name} returns ${r}`)
  })))

const waiters = (pool: any) => pool.state.waiters.size
const exitText = (exit: any): string =>
  exit._tag === "Success"
    ? `success ${String(exit.value)}`
    : `failure ${(exit.cause.reasons ?? []).map((r: any) => r._tag === "Fail" ? `Fail ${String(r.error)}` : r._tag).join(", ")}`

// PP1. A healthy return keeps the resource. Size 1. A borrows and returns, then B borrows and
// returns. The pool's scope then closes.
const pp1 = Effect.gen(function*() {
  const log: Array<string> = []
  const { pool, scope } = yield* openPool({ acquire: resource(log), size: 1 })
  yield* borrower(pool, "A", log)
  yield* settle
  yield* borrower(pool, "B", log)
  yield* settle
  log.push("the pool's scope closes")
  yield* Scope.close(scope, Exit.void)
  yield* settle
  return { log }
})

// PP2. The order of reuse. Size 2. A and B hold one item each. A returns, then B returns. C then
// borrows, and D borrows while C holds.
const pp2 = Effect.gen(function*() {
  const log: Array<string> = []
  const { pool, scope } = yield* openPool({ acquire: resource(log), size: 2 })
  const gA = yield* Deferred.make()
  const gB = yield* Deferred.make()
  const gC = yield* Deferred.make()
  const gD = yield* Deferred.make()
  yield* borrower(pool, "A", log, gA)
  yield* settle
  yield* borrower(pool, "B", log, gB)
  yield* settle
  yield* Deferred.succeed(gA, undefined)
  yield* settle
  yield* Deferred.succeed(gB, undefined)
  yield* settle
  yield* borrower(pool, "C", log, gC)
  yield* settle
  yield* borrower(pool, "D", log, gD)
  yield* settle
  const afterReuse = log.filter((l) => l.startsWith("C got") || l.startsWith("D got"))
  yield* Deferred.succeed(gC, undefined)
  yield* Deferred.succeed(gD, undefined)
  yield* settle
  yield* Scope.close(scope, Exit.void)
  yield* settle
  return { afterReuse, log }
})

// PP3. One return wakes one waiter. Size 1. H holds the item. A waits, then B waits. Both hold
// what they get. H returns.
const pp3 = Effect.gen(function*() {
  const log: Array<string> = []
  const { pool, scope } = yield* openPool({ acquire: resource(log), size: 1 })
  const gH = yield* Deferred.make()
  const gA = yield* Deferred.make()
  const gB = yield* Deferred.make()
  yield* borrower(pool, "H", log, gH)
  yield* settle
  yield* borrower(pool, "A", log, gA)
  yield* settle
  yield* borrower(pool, "B", log, gB)
  yield* settle
  const waitingBefore = waiters(pool)
  yield* Deferred.succeed(gH, undefined)
  yield* settle
  const waitingAfterOneReturn = waiters(pool)
  const logAfterOneReturn = log.slice()
  yield* Deferred.succeed(gA, undefined)
  yield* settle
  yield* Deferred.succeed(gB, undefined)
  yield* settle
  yield* Scope.close(scope, Exit.void)
  yield* settle
  return { waitingBefore, waitingAfterOneReturn, logAfterOneReturn, log }
})

// PP4. When does a wake choose its waiters? Size 1. H holds the item. A waits, then B waits. H
// returns, which posts the wake. Before the posted task runs, A is interrupted.
const pp4 = Effect.gen(function*() {
  const log: Array<string> = []
  const { pool, scope } = yield* openPool({ acquire: resource(log), size: 1 })
  const gH = yield* Deferred.make()
  const gB = yield* Deferred.make()
  yield* borrower(pool, "H", log, gH)
  yield* settle
  const a: any = yield* borrower(pool, "A", log)
  yield* settle
  yield* borrower(pool, "B", log, gB)
  yield* settle
  const waitingBefore = waiters(pool)
  // One stretch with no yield: H's return posts the wake, and A leaves before the task runs.
  yield* Effect.sync(() => {
    Effect.runSync(Deferred.succeed(gH, undefined))
    log.push(`after H's return and before the task: ${waiters(pool)} waiting`)
    a.interruptUnsafe()
    log.push(`after A's interruption and before the task: ${waiters(pool)} waiting`)
  })
  yield* settle
  const logAfterTheTask = log.slice()
  yield* Deferred.succeed(gB, undefined)
  yield* settle
  yield* Scope.close(scope, Exit.void)
  yield* settle
  return { waitingBefore, logAfterTheTask, log }
})

// PP5. A wake notifies; it hands out no item. Size 1, and the acquisition waits for a gate. A and
// B ask before any item exists. A returns at once, and B holds. The gate opens.
const pp5 = Effect.gen(function*() {
  const log: Array<string> = []
  const gAcquire = yield* Deferred.make()
  const { pool, scope } = yield* openPool({ acquire: resource(log, Deferred.await(gAcquire)), size: 1 })
  const gB = yield* Deferred.make()
  yield* borrower(pool, "A", log)
  yield* settle
  yield* borrower(pool, "B", log, gB)
  yield* settle
  const waitingBefore = waiters(pool)
  yield* Deferred.succeed(gAcquire, undefined)
  yield* settle
  const logAfterTheWake = log.slice()
  const waitingAfter = waiters(pool)
  yield* Deferred.succeed(gB, undefined)
  yield* settle
  yield* Scope.close(scope, Exit.void)
  yield* settle
  return { waitingBefore, logAfterTheWake, waitingAfter, log }
})

// PP6. An acquisition that fails after it registered a cleanup. Size 1. The first acquisition
// registers a cleanup and fails. Later ones succeed. A borrows, then B borrows.
const pp6 = Effect.gen(function*() {
  const log: Array<string> = []
  let attempt = 0
  const good = resource(log)
  const acquire = Effect.suspend(() => {
    attempt++
    if (attempt > 1) return good
    return Effect.flatMap(
      Effect.acquireRelease(
        Effect.sync(() => { log.push("the failing acquisition registers a cleanup") }),
        () => Effect.sync(() => { log.push("the failing acquisition's cleanup runs") })
      ),
      () => Effect.fail("boom")
    )
  })
  const { pool, scope } = yield* openPool({ acquire, size: 1 })
  const exitA = yield* Effect.exit(Effect.scoped(Pool.get(pool)))
  log.push(`A: ${exitText(exitA)}`)
  yield* settle
  const exitB = yield* Effect.exit(Effect.scoped(Pool.get(pool)))
  log.push(`B: ${exitText(exitB)}`)
  yield* settle
  log.push("the pool's scope closes")
  yield* Scope.close(scope, Exit.void)
  yield* settle
  return { acquisitions: attempt, log }
})

// PP7. The pool's scope closes while one borrower holds and one waits. Size 1.
const pp7 = Effect.gen(function*() {
  const log: Array<string> = []
  const { pool, scope } = yield* openPool({ acquire: resource(log), size: 1 })
  const gH = yield* Deferred.make()
  yield* borrower(pool, "H", log, gH)
  yield* settle
  const w = yield* fork(Effect.exit(Effect.scoped(Effect.gen(function*() {
    const r = yield* Pool.get(pool)
    log.push(`W got ${r}`)
  }))))
  yield* settle
  let closed = false
  yield* fork(Effect.gen(function*() {
    log.push("the pool's scope starts to close")
    yield* Scope.close(scope, Exit.void)
    closed = true
    log.push("the pool's scope is closed")
  }))
  yield* settle
  const whileHHolds = { closed, waiting: waiters(pool), log: log.slice() }
  yield* Deferred.succeed(gH, undefined)
  yield* settle
  const exitW: any = w.pollUnsafe()
  return { whileHHolds, closedAfterTheReturn: closed, waiter: exitW ? exitText(exitW.value ?? exitW) : "still running", log }
})

// PP8. A waiter is interrupted. Size 1. H holds. A waits and is interrupted. H returns, and B
// borrows.
const pp8 = Effect.gen(function*() {
  const log: Array<string> = []
  const { pool, scope } = yield* openPool({ acquire: resource(log), size: 1 })
  const gH = yield* Deferred.make()
  yield* borrower(pool, "H", log, gH)
  yield* settle
  const a: any = yield* borrower(pool, "A", log)
  yield* settle
  const waitingWhileAWaits = waiters(pool)
  yield* Effect.sync(() => a.interruptUnsafe())
  yield* settle
  const waitingAfterAInterrupted = waiters(pool)
  yield* Deferred.succeed(gH, undefined)
  yield* settle
  yield* borrower(pool, "B", log)
  yield* settle
  yield* Scope.close(scope, Exit.void)
  yield* settle
  return { waitingWhileAWaits, waitingAfterAInterrupted, log }
})

const run = (e: any) => Effect.runPromise(e).catch((error: unknown) => ({ probeError: String(error) }))
const out = {
  effect: version,
  runtime: `bun ${Bun.version}`,
  pp1_healthy_return: await run(pp1),
  pp2_order_of_reuse: await run(pp2),
  pp3_one_return_wakes_one: await run(pp3),
  pp4_when_a_wake_chooses: await run(pp4),
  pp5_a_wake_hands_out_nothing: await run(pp5),
  pp6_failed_acquisition: await run(pp6),
  pp7_close_with_a_holder_and_a_waiter: await run(pp7),
  pp8_waiter_interrupted: await run(pp8)
}
console.log(JSON.stringify(out, null, 1))
