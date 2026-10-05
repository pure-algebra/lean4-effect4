// The native queue's answer on the cancel-after-signal control of composite-queue.ts (2026-10-05).
// Run: EFFECT_DIR=<an effect package directory> bun run native-cancel-after-signal.ts
// Two takers wait. A message is offered, so the first taker's wake is posted. The first taker is
// interrupted before that wake runs. Who receives the message?
import { readFileSync } from "node:fs"
const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const { Effect, Fiber, Queue } = await import(`${dir}/dist/index.js`)
const settle = Effect.gen(function*() {
  for (let i = 0; i < 8; i++) yield* Effect.yieldNow
})
const main = Effect.gen(function*() {
  const q = yield* Queue.unbounded()
  let second: unknown = "waiting"
  const t1 = yield* Effect.forkChild(Queue.take(q))
  yield* settle
  const t2 = yield* Effect.forkChild(Effect.gen(function*() {
    second = yield* Queue.take(q)
  }))
  yield* settle
  yield* Queue.offer(q, 1)
  yield* Fiber.interrupt(t1)
  yield* settle
  const out = { effect: version, secondTaker: second, left: yield* Queue.size(q) }
  yield* Fiber.interrupt(t2)
  return out
})
Effect.runPromise(main).then((r: unknown) => console.log(JSON.stringify(r)))
