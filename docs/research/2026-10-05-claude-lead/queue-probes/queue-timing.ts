// Queue timing probes over one Effect build (2026-10-05). Finite host runs, not proofs.
//
// Run: EFFECT_DIR=<an effect package directory> bun run queue-timing.ts
// Each probe parks one taker, then lets one fiber offer twice. `gap` says whether that fiber
// yields between its two offers. The question: does the taker's answer depend on the gap?
import { existsSync, readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const entry = existsSync(`${dir}/dist/index.js`) ? `${dir}/dist/index.js` : `${dir}/dist/esm/index.js`
const { Effect, Fiber, Queue } = await import(entry)

const v4 = typeof Effect.forkChild === "function"
const fork = v4 ? Effect.forkChild : Effect.fork
const yieldNow = v4 ? Effect.yieldNow : Effect.yieldNow()
const settle = Effect.gen(function*() {
  for (let i = 0; i < 6; i++) yield* yieldNow
})
const show = (r: unknown) => r === "waiting" ? r : Array.isArray(r) ? r : Array.from(r as Iterable<unknown>)

// P5. An unbounded queue. One taker parks in takeBetween(1, 2). One fiber offers 1, then 2.
const p5 = (gap: boolean) =>
  Effect.gen(function*() {
    const q = yield* Queue.unbounded()
    let result: unknown = "waiting"
    const f = yield* fork(Effect.gen(function*() {
      result = yield* Queue.takeBetween(q, 1, 2)
    }))
    yield* settle
    yield* Queue.offer(q, 1)
    if (gap) yield* settle
    yield* Queue.offer(q, 2)
    yield* settle
    const left = yield* Queue.size(q)
    yield* Fiber.interrupt(f)
    return { gap, taker: show(result), left }
  })

// P6. A sliding queue of capacity one. One taker parks in take. One fiber offers 1, then 2.
const p6 = (gap: boolean) =>
  Effect.gen(function*() {
    const q = yield* Queue.sliding(1)
    let result: unknown = "waiting"
    const f = yield* fork(Effect.gen(function*() {
      result = yield* Queue.take(q)
    }))
    yield* settle
    yield* Queue.offer(q, 1)
    if (gap) yield* settle
    yield* Queue.offer(q, 2)
    yield* settle
    const left = yield* Queue.size(q)
    yield* Fiber.interrupt(f)
    return { gap, taker: result, left }
  })

// P7. A dropping queue of capacity one. One taker parks in take. One fiber offers 1, then 2.
// The second offer's own answer is the observation.
const p7 = (gap: boolean) =>
  Effect.gen(function*() {
    const q = yield* Queue.dropping(1)
    let result: unknown = "waiting"
    const f = yield* fork(Effect.gen(function*() {
      result = yield* Queue.take(q)
    }))
    yield* settle
    const first = yield* Queue.offer(q, 1)
    if (gap) yield* settle
    const second = yield* Queue.offer(q, 2)
    yield* settle
    const left = yield* Queue.size(q)
    yield* Fiber.interrupt(f)
    return { gap, taker: result, offers: [first, second], left }
  })

const main = Effect.gen(function*() {
  const out: Record<string, unknown> = { effect: version }
  out.p5_batchOneToTwo = [yield* p5(false), yield* p5(true)]
  out.p6_slidingOne = [yield* p6(false), yield* p6(true)]
  out.p7_droppingOne = [yield* p7(false), yield* p7(true)]
  return out
})

Effect.runPromise(main).then((r: unknown) => console.log(JSON.stringify(r)))
