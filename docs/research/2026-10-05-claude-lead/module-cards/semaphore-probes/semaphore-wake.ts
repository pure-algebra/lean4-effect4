// Semaphore probes over one Effect build (2026-10-06). Finite host runs, not proofs.
//
// Run: EFFECT_DIR=<an effect package directory> bun run semaphore-wake.ts
// The package directory is the one that holds package.json and dist/index.js.
// Each probe is one schedule. The output names the build's version.
import { existsSync, readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
// Effect 3 ships its entry under dist/esm; Effect 4 under dist.
const entry = existsSync(`${dir}/dist/index.js`) ? `${dir}/dist/index.js` : `${dir}/dist/esm/index.js`
const E = await import(entry)
const { Effect, Fiber, Deferred } = E

const v4 = typeof Effect.forkChild === "function"
const fork = v4 ? Effect.forkChild : Effect.fork
const yieldNow = v4 ? Effect.yieldNow : Effect.yieldNow()
const makeSemaphore = (n: number) => (v4 ? E.Semaphore.make(n) : Effect.makeSemaphore(n))
const settle = Effect.gen(function*() {
  for (let i = 0; i < 16; i++) yield* yieldNow
})

// The semaphore's three fields, read from the object. Both builds name them alike.
const state = (sem: any) => ({ permits: sem.permits, taken: sem.taken, waiters: sem.waiters.size })

// The class reads its free count through a getter. This replaces the getter on one object with
// the same subtraction, and it records each read while `on` is true. The log then shows where
// the walk reads the count, and where a waiter's retry reads it.
const traceFree = (sem: any, log: Array<string>) => {
  const flag = { on: false }
  Object.defineProperty(sem, "free", {
    configurable: true,
    get() {
      const v = this.permits - this.taken
      if (flag.on) log.push(`free read ${v}`)
      return v
    }
  })
  return flag
}

// P1. The protected case at a total of 2. A holds 2 inside a protected body. B asks for 2, then
// C asks for 1, by the raw operation. Both wait, B before C. A's body ends, and its hook
// releases 2. Does B's retry take before the walk reads the count for C?
const p1 = Effect.gen(function*() {
  const sem: any = yield* makeSemaphore(2)
  const log: Array<string> = []
  const gate = yield* Deferred.make()
  const a = yield* fork(sem.withPermits(2)(Deferred.await(gate)))
  yield* settle
  const b = yield* fork(Effect.gen(function*() {
    yield* sem.take(2)
    log.push("B took 2")
  }))
  yield* settle
  const c = yield* fork(Effect.gen(function*() {
    yield* sem.take(1)
    log.push("C took 1")
  }))
  yield* settle
  const before = state(sem)
  const observersBefore = Array.from(sem.waiters)
  const flag = traceFree(sem, log)
  flag.on = true
  yield* Deferred.succeed(gate, undefined)
  yield* settle
  flag.on = false
  const observersAfter = Array.from(sem.waiters)
  const after = state(sem)
  yield* Fiber.interrupt(a)
  yield* Fiber.interrupt(b)
  yield* Fiber.interrupt(c)
  return {
    before,
    trace: log,
    after,
    cObserverIsTheSameObject: observersAfter.includes(observersBefore[1])
  }
})

// P2. The scan case at a total of 2. A and D hold 1 each. B asks for 2, then C asks for 1.
// A releases 1. Does the walk pass B and serve C?
const p2 = Effect.gen(function*() {
  const sem: any = yield* makeSemaphore(2)
  const log: Array<string> = []
  yield* sem.take(1)
  yield* sem.take(1)
  const b = yield* fork(Effect.gen(function*() {
    yield* sem.take(2)
    log.push("B took 2")
  }))
  yield* settle
  const c = yield* fork(Effect.gen(function*() {
    yield* sem.take(1)
    log.push("C took 1")
  }))
  yield* settle
  const before = state(sem)
  const observersBefore = Array.from(sem.waiters)
  const flag = traceFree(sem, log)
  flag.on = true
  const answer = yield* sem.release(1)
  yield* settle
  flag.on = false
  const observersAfter = Array.from(sem.waiters)
  const after = state(sem)
  yield* Fiber.interrupt(b)
  yield* Fiber.interrupt(c)
  return {
    before,
    releaseAnswered: answer,
    trace: log,
    after,
    bObserverIsTheSameObject: observersAfter.includes(observersBefore[0])
  }
})

// P3. The overtaking case at a total of 2. H holds 2. B asks for 1 and, with no yield, asks for
// 1 again. C asks for 1 after B. H releases 2. Who holds the two permits?
const p3 = Effect.gen(function*() {
  const sem: any = yield* makeSemaphore(2)
  const log: Array<string> = []
  yield* sem.take(2)
  const b = yield* fork(Effect.gen(function*() {
    yield* sem.take(1)
    log.push("B took 1")
    yield* sem.take(1)
    log.push("B took 1 again")
  }))
  yield* settle
  const c = yield* fork(Effect.gen(function*() {
    yield* sem.take(1)
    log.push("C took 1")
  }))
  yield* settle
  const before = state(sem)
  const flag = traceFree(sem, log)
  flag.on = true
  yield* sem.release(2)
  yield* settle
  flag.on = false
  const after = state(sem)
  yield* Fiber.interrupt(b)
  yield* Fiber.interrupt(c)
  return { before, trace: log, after }
})

// P4. Two protected waiters with bodies that do not wait, at a total of 2. A holds 2 inside a
// protected body. B asks for 2 and C asks for 1, both protected. A's body ends.
const p4 = Effect.gen(function*() {
  const sem: any = yield* makeSemaphore(2)
  const log: Array<string> = []
  const gate = yield* Deferred.make()
  const a = yield* fork(sem.withPermits(2)(Deferred.await(gate)))
  yield* settle
  const b = yield* fork(sem.withPermits(2)(Effect.sync(() => {
    log.push(`B body, taken ${sem.taken}`)
  })))
  yield* settle
  const c = yield* fork(sem.withPermits(1)(Effect.sync(() => {
    log.push(`C body, taken ${sem.taken}`)
  })))
  yield* settle
  const before = state(sem)
  const flag = traceFree(sem, log)
  flag.on = true
  yield* Deferred.succeed(gate, undefined)
  yield* settle
  flag.on = false
  const after = state(sem)
  yield* Fiber.interrupt(a)
  yield* Fiber.interrupt(b)
  yield* Fiber.interrupt(c)
  return { before, trace: log, after }
})

// P5. A release with nothing taken, at a total of 2. How many takers of 1 then proceed?
const p5 = Effect.gen(function*() {
  const sem: any = yield* makeSemaphore(2)
  const answer = yield* sem.release(1)
  const afterRelease = state(sem)
  let proceeded = 0
  const takers: Array<any> = []
  for (let i = 0; i < 4; i++) {
    takers.push(
      yield* fork(Effect.gen(function*() {
        yield* sem.take(1)
        proceeded++
      }))
    )
  }
  yield* settle
  const after = state(sem)
  for (const t of takers) yield* Fiber.interrupt(t)
  return { releaseAnswered: answer, afterRelease, takersOfOneThatProceeded: proceeded, after }
})

// P6. A negative count and a fraction, at a total of 2.
const p6 = Effect.gen(function*() {
  const sem: any = yield* makeSemaphore(2)
  const n = yield* sem.take(-1)
  const afterNegative = state(sem)
  const h = yield* sem.take(0.5)
  const afterFraction = state(sem)
  return { takeMinusOneAnswered: n, afterNegative, takeHalfAnswered: h, afterFraction }
})

// P7. A waiter is interrupted, at a total of 1. H holds 1. B waits by the raw operation and is
// interrupted. C waits in the protected form and is interrupted. H then releases 1.
const p7 = Effect.gen(function*() {
  const sem: any = yield* makeSemaphore(1)
  yield* sem.take(1)
  const b = yield* fork(sem.take(1))
  yield* settle
  const whileBWaits = state(sem)
  yield* Fiber.interrupt(b)
  const afterBInterrupted = state(sem)
  const c = yield* fork(sem.withPermits(1)(Effect.never))
  yield* settle
  const whileCWaits = state(sem)
  yield* Fiber.interrupt(c)
  const afterCInterrupted = state(sem)
  yield* sem.release(1)
  yield* settle
  return { whileBWaits, afterBInterrupted, whileCWaits, afterCInterrupted, afterRelease: state(sem) }
})

// P8. A protected body is interrupted, at a total of 1. Then `releaseAll` runs while another
// protected body holds its permit, and that body ends.
const p8 = Effect.gen(function*() {
  const sem: any = yield* makeSemaphore(1)
  const a = yield* fork(sem.withPermits(1)(Effect.never))
  yield* settle
  const whileAHolds = state(sem)
  yield* Fiber.interrupt(a)
  const afterAInterrupted = state(sem)
  const gate = yield* Deferred.make()
  const d = yield* fork(sem.withPermits(1)(Deferred.await(gate)))
  yield* settle
  const releaseAllAnswered = yield* sem.releaseAll
  const afterReleaseAll = state(sem)
  yield* Deferred.succeed(gate, undefined)
  yield* settle
  const afterBodyEnds = state(sem)
  yield* Fiber.interrupt(d)
  return { whileAHolds, afterAInterrupted, releaseAllAnswered, afterReleaseAll, afterBodyEnds }
})

// P9. The protected case of P1, with one change: B runs under a scheduler that tells it to yield
// once, at the moment the walk resumes it. Does the walk go on to C? Effect 4 only: the
// scheduler is a service there, and its `shouldYield` is the run loop's question.
const p9 = Effect.gen(function*() {
  const sem: any = yield* makeSemaphore(2)
  const log: Array<string> = []
  const gate = yield* Deferred.make()
  const a = yield* fork(sem.withPermits(2)(Deferred.await(gate)))
  yield* settle
  const once = { armed: false }
  const base = new E.Scheduler.MixedScheduler()
  const yielding = {
    executionMode: base.executionMode,
    makeDispatcher: () => base.makeDispatcher(),
    shouldYield: (fiber: any) => {
      if (once.armed) {
        once.armed = false
        log.push("the scheduler tells B to yield")
        return true
      }
      return base.shouldYield(fiber)
    }
  }
  const b = yield* fork(Effect.provideService(
    Effect.gen(function*() {
      yield* sem.take(2)
      log.push("B took 2")
    }),
    E.Scheduler.Scheduler,
    yielding
  ))
  yield* settle
  const c = yield* fork(Effect.gen(function*() {
    yield* sem.take(1)
    log.push("C took 1")
  }))
  yield* settle
  const before = state(sem)
  const observersBefore = Array.from(sem.waiters)
  const flag = traceFree(sem, log)
  flag.on = true
  once.armed = true
  yield* Deferred.succeed(gate, undefined)
  yield* settle
  flag.on = false
  const observersAfter = Array.from(sem.waiters)
  const after = state(sem)
  yield* Fiber.interrupt(a)
  yield* Fiber.interrupt(b)
  yield* Fiber.interrupt(c)
  return {
    before,
    trace: log,
    after,
    bObserverIsTheSameObject: observersAfter.includes(observersBefore[0])
  }
})

const run = (e: any) => Effect.runPromise(e)
const out = {
  effect: version,
  runtime: `bun ${Bun.version}`,
  p1_protected: await run(p1),
  p2_scan: await run(p2),
  p3_overtaking: await run(p3),
  p4_protected_waiters: await run(p4),
  p5_release_with_nothing_taken: await run(p5),
  p6_negative_and_fraction: await run(p6),
  p7_waiter_interrupted: await run(p7),
  p8_protected_interrupted_and_releaseAll: await run(p8),
  p9_waiter_yields_before_its_retry: v4 ? await run(p9) : "not run: Effect 4 only"
}
console.log(JSON.stringify(out, null, 1))
