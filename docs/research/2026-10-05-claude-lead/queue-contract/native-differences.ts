// Where the native queue differs from the contract of queue-contract.md (2026-10-05).
// Finite host runs on one Effect 4 build, not proofs.
// Run: EFFECT_DIR=<an effect package directory> bun run native-differences.ts
import { readFileSync } from "node:fs"
const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const { Effect, Fiber, Queue, Option } = await import(`${dir}/dist/index.js`)
const settle = Effect.gen(function*() {
  for (let i = 0; i < 8; i++) yield* Effect.yieldNow
})
const show = (o: any) => (Option.isSome(o) ? `some(${o.value})` : "none")

// D1. Capacity one holds 1. An offerer waits with 2 and then offers 3. One fiber then runs
// take, take, poll with no yield between. The native queue resumes a waiting offerer inside
// the take that frees room.
const d1 = Effect.gen(function*() {
  const q = yield* Queue.bounded(1)
  yield* Queue.offer(q, 1)
  const o = yield* Effect.forkChild(Effect.gen(function*() {
    yield* Queue.offer(q, 2)
    yield* Queue.offer(q, 3)
  }))
  yield* settle
  const a = yield* Queue.take(q)
  const b = yield* Queue.take(q)
  const c = yield* Queue.poll(q)
  yield* settle
  yield* Fiber.interrupt(o)
  return [a, b, show(c)]
})

// D2. Capacity zero. A taker waits; one fiber offers 1 and records when its offer answers.
const d2 = Effect.gen(function*() {
  const q = yield* Queue.bounded(0)
  const log: Array<string> = []
  const t = yield* Effect.forkChild(Effect.gen(function*() {
    log.push(`taker got ${yield* Queue.take(q)}`)
  }))
  yield* settle
  const ok = yield* Queue.offer(q, 1)
  log.push(`offer answered ${ok}`)
  yield* settle
  yield* Fiber.interrupt(t)
  return log
})

// D3. Capacity zero. A taker waits; offerAll([1, 2]) is forked; the taker is interrupted
// before the posted wake runs. How many messages does the queue of capacity zero buffer?
const d3 = Effect.gen(function*() {
  const q = yield* Queue.bounded(0)
  const t = yield* Effect.forkChild(Queue.take(q))
  yield* settle
  const o = yield* Effect.forkChild(Queue.offerAll(q, [1, 2]), { startImmediately: true })
  yield* Fiber.interrupt(t)
  yield* settle
  const size = yield* Queue.size(q)
  yield* Fiber.interrupt(o)
  return { bufferedAtCapacityZero: size }
})

// D4. Dropping at capacity zero: an offer with a taker waiting, and one with none. The log
// records whether the taker receives its message before the offer answers.
const d4 = Effect.gen(function*() {
  const q = yield* Queue.dropping(0)
  const none = yield* Queue.offer(q, 1)
  let got: unknown = "waiting"
  const order: Array<string> = []
  const t = yield* Effect.forkChild(Effect.gen(function*() {
    got = yield* Queue.take(q)
    order.push(`taker got ${got}`)
  }))
  yield* settle
  order.push("before offer")
  const withTaker = yield* Queue.offer(q, 2)
  order.push(`offer answered ${withTaker}`)
  yield* settle
  yield* Fiber.interrupt(t)
  return { offerWithNoTaker: none, offerWithTaker: withTaker, taker: got, order }
})

// D5. Sliding at capacity zero: a taker waits, and a message is offered.
const d5 = Effect.gen(function*() {
  const q = yield* Queue.sliding(0)
  let got: unknown = "waiting"
  const t = yield* Effect.forkChild(Effect.gen(function*() {
    got = yield* Queue.take(q)
  }))
  yield* settle
  const ok = yield* Queue.offer(q, 1)
  yield* settle
  const out = { offer: ok, taker: got, size: yield* Queue.size(q) }
  yield* Fiber.interrupt(t)
  return out
})

// D6. A take of three waits with one message buffered. A clear then runs.
const d6 = Effect.gen(function*() {
  const q = yield* Queue.unbounded()
  yield* Queue.offer(q, 1)
  const t = yield* Effect.forkChild(Queue.takeBetween(q, 3, 5))
  yield* settle
  const cleared = yield* Queue.clear(q)
  yield* Fiber.interrupt(t)
  return { cleared: Array.from(cleared as Iterable<unknown>) }
})

// D7. Capacity zero. A peek waits; a message is offered.
const d7 = Effect.gen(function*() {
  const q = yield* Queue.bounded(0)
  let saw: unknown = "waiting"
  const p = yield* Effect.forkChild(Effect.gen(function*() {
    saw = yield* Queue.peek(q)
  }))
  yield* settle
  const o = yield* Effect.forkChild(Queue.offer(q, 1), { startImmediately: true })
  yield* settle
  const out = { peek: saw, size: yield* Queue.size(q), offerDone: o.pollUnsafe() !== undefined }
  yield* Fiber.interrupt(p)
  yield* Fiber.interrupt(o)
  return out
})

// D8. A take of three waits with one message buffered. A poll then runs. A second queue has
// no taker, as the positive control.
const d8 = Effect.gen(function*() {
  const q = yield* Queue.unbounded()
  yield* Queue.offer(q, 1)
  const t = yield* Effect.forkChild(Queue.takeBetween(q, 3, 5))
  yield* settle
  const polled = yield* Queue.poll(q)
  const size = yield* Queue.size(q)
  const waiting = t.pollUnsafe() === undefined
  yield* Fiber.interrupt(t)
  const q2 = yield* Queue.unbounded()
  yield* Queue.offer(q2, 1)
  return { pollPastTaker: show(polled), sizeAfter: size, takerStillWaits: waiting,
    pollWithNoTaker: show(yield* Queue.poll(q2)) }
})

// D9. Capacity zero. An offer waits; a clear then runs. An empty queue is the control.
const d9 = Effect.gen(function*() {
  const q = yield* Queue.bounded(0)
  const o = yield* Effect.forkChild(Queue.offer(q, 1), { startImmediately: true })
  yield* settle
  const cleared = yield* Queue.clear(q)
  yield* settle
  const done = o.pollUnsafe() !== undefined
  yield* Fiber.interrupt(o)
  const q2 = yield* Queue.bounded(0)
  return { cleared: Array.from(cleared as Iterable<unknown>), offerDone: done,
    clearedEmpty: Array.from((yield* Queue.clear(q2)) as Iterable<unknown>) }
})

// D10. Capacity two. A batch of four is offered; one take; the waiting producer is
// interrupted; a clear reads what was accepted. The second run takes twice and does not
// interrupt.
const d10 = Effect.gen(function*() {
  const q = yield* Queue.bounded(2)
  const o = yield* Effect.forkChild(Queue.offerAll(q, [1, 2, 3, 4]), { startImmediately: true })
  yield* settle
  const a = yield* Queue.take(q)
  yield* Fiber.interrupt(o)
  const left = Array.from((yield* Queue.clear(q)) as Iterable<unknown>)
  const q2 = yield* Queue.bounded(2)
  const o2 = yield* Effect.forkChild(Queue.offerAll(q2, [1, 2, 3, 4]), { startImmediately: true })
  yield* settle
  const b1 = yield* Queue.take(q2)
  const b2 = yield* Queue.take(q2)
  yield* settle
  const answered = o2.pollUnsafe() !== undefined
  const left2 = Array.from((yield* Queue.clear(q2)) as Iterable<unknown>)
  yield* Fiber.interrupt(o2)
  return { took: a, afterInterrupt: left, tookTwice: [b1, b2], producerAnswered: answered,
    afterBoth: left2 }
})

const main = Effect.gen(function*() {
  const out: Record<string, unknown> = { effect: version }
  out.d1_offererResumedInside = yield* d1
  out.d2_rendezvousOrder = yield* d2
  out.d3_offerAllCountsTakers = yield* d3
  out.d4_droppingZero = yield* d4
  out.d5_slidingZero = yield* d5
  out.d6_clearPassesTaker = yield* d6
  out.d7_peekAtZero = yield* d7
  out.d8_pollPassesTaker = yield* d8
  out.d9_clearAtZero = yield* d9
  out.d10_batchPrefix = yield* d10
  return out
})
Effect.runPromise(main).then((r: unknown) => console.log(JSON.stringify(r)))
