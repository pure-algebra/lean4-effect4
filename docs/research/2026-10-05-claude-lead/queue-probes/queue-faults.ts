// Queue probes over one Effect build (2026-10-05). Finite host runs, not proofs.
//
// Run: EFFECT_DIR=<an effect package directory> bun run queue-faults.ts
// The package directory is the one that holds package.json and dist/index.js.
// Each probe states what a fair, documented queue would answer.
import { existsSync, readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
// Effect 3 ships its entry under dist/esm; Effect 4 under dist.
const entry = existsSync(`${dir}/dist/index.js`) ? `${dir}/dist/index.js` : `${dir}/dist/esm/index.js`
const { Effect, Fiber, Queue } = await import(entry)

const v4 = typeof Effect.forkChild === "function"
const fork = v4 ? Effect.forkChild : Effect.fork
const yieldNow = v4 ? Effect.yieldNow : Effect.yieldNow()
const settle = Effect.gen(function*() {
  for (let i = 0; i < 6; i++) yield* yieldNow
})

// P1. A parks first on an empty queue. B then takes in a loop and yields after each take.
// The main fiber offers one message per round and yields. A fair queue serves A first.
const p1 = (bYieldsFirst: boolean) =>
  Effect.gen(function*() {
    const rounds = 6
    const q = yield* Queue.unbounded()
    const log: Array<string> = []
    const a = yield* fork(Effect.gen(function*() {
      const m = yield* Queue.take(q)
      log.push(`A got ${m}`)
    }))
    yield* yieldNow
    const b = yield* fork(Effect.gen(function*() {
      if (bYieldsFirst) yield* yieldNow
      for (let i = 0; i < rounds; i++) {
        const m = yield* Queue.take(q)
        log.push(`B got ${m}`)
        yield* yieldNow
      }
    }))
    for (let i = 1; i <= rounds; i++) {
      yield* Queue.offer(q, i)
      yield* yieldNow
    }
    yield* settle
    const count = (who: string) => log.filter((l) => l.startsWith(who)).length
    yield* Fiber.interrupt(a)
    yield* Fiber.interrupt(b)
    return { aGot: count("A got"), bGot: count("B got"), order: log.join(", ") }
  })

// P2. takeBetween(min, max) parks on an empty queue; messages arrive one at a time.
// The documentation says it waits while fewer than `min` messages are available.
const p2 = (min: number, max: number, arrivals: ReadonlyArray<number>) =>
  Effect.gen(function*() {
    const q = yield* Queue.unbounded()
    let result: unknown = "waiting"
    const f = yield* fork(Effect.gen(function*() {
      result = yield* Queue.takeBetween(q, min, max)
    }))
    yield* settle
    const seen: Array<unknown> = []
    for (const m of arrivals) {
      yield* Queue.offer(q, m)
      yield* settle
      seen.push(result === "waiting" ? result : Array.from(result as Iterable<number>))
    }
    yield* Fiber.interrupt(f)
    return { min, max, afterEachArrival: seen }
  })

// P3 (Effect 4 only). One message is buffered. takeBetween(3, 5) parks. The queue then ends.
// A queue that ends should release the parked taker with what is left.
const p3 = Effect.gen(function*() {
  const q = yield* Queue.unbounded()
  yield* Queue.offer(q, 1)
  let result: unknown = "waiting"
  const f = yield* fork(Effect.gen(function*() {
    result = yield* Effect.exit(Queue.takeBetween(q, 3, 5))
  }))
  yield* settle
  const ended = yield* Queue.end(q)
  yield* settle
  const out = { ended, takerAfterEnd: result === "waiting" ? result : JSON.parse(JSON.stringify(result)) }
  yield* Fiber.interrupt(f)
  return out
})

// P4 (Effect 4 only). bounded(1) holds `a`. An offer of `b` parks. The queue ends, so it is
// closing. The parked offerer is interrupted. Then the queue is drained.
// An interrupted offer should not deliver its message afterwards.
const p4 = Effect.gen(function*() {
  const q = yield* Queue.bounded(1)
  yield* Queue.offer(q, "a")
  const offerer = yield* fork(Queue.offer(q, "b"))
  yield* settle
  yield* Queue.end(q)
  yield* settle
  yield* Fiber.interrupt(offerer)
  yield* settle
  const first = yield* Effect.exit(Queue.take(q))
  yield* settle
  let second: unknown = "waiting"
  const t = yield* fork(Effect.gen(function*() {
    second = yield* Effect.exit(Queue.take(q))
  }))
  yield* settle
  const out = {
    first: JSON.parse(JSON.stringify(first)),
    second: second === "waiting" ? second : JSON.parse(JSON.stringify(second))
  }
  yield* Fiber.interrupt(t)
  return out
})

const main = Effect.gen(function*() {
  const out: Record<string, unknown> = { effect: version }
  out.p1_bStartsAtOnce = yield* p1(false)
  out.p1_bYieldsFirst = yield* p1(true)
  out.p2_min3 = yield* p2(3, 5, [1, 2, 3])
  out.p2_min2 = yield* p2(2, 5, [1, 2])
  if (v4) {
    out.p3_endWhileBatchTakerParked = yield* p3
    out.p4_interruptedOfferInClosing = yield* p4
  }
  return out
})

Effect.runPromise(main).then((r: unknown) => console.log(JSON.stringify(r, null, 1)))
