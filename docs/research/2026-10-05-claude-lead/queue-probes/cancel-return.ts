// Cancellation after consumption, over one Effect build (2026-10-05). Finite host runs.
//
// Run: EFFECT_DIR=<an effect package directory> bun run cancel-return.ts
// An independent replication of Codex's probe (atomic/cancel-return in its packet), on the
// default scheduler. A protected body takes a message and reaches its result. Another fiber
// asks for the interrupt while the body is still protected. Four things are observed apart:
// the consumption, the operation's exit, the caller's continuation, and the fiber's exit.
import { existsSync, readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const entry = existsSync(`${dir}/dist/index.js`) ? `${dir}/dist/index.js` : `${dir}/dist/esm/index.js`
const { Effect, Fiber, Queue, Deferred, Exit, Cause } = await import(entry)

const v4 = typeof Effect.forkChild === "function"
const fork = v4 ? Effect.forkChild : Effect.fork
const yieldNow = v4 ? Effect.yieldNow : Effect.yieldNow()
const settle = Effect.gen(function*() {
  for (let i = 0; i < 8; i++) yield* yieldNow
})
const showExit = (x: any) =>
  x._tag === "Success"
    ? `Success(${x.value})`
    : (v4 ? x.cause.reasons.map((r: any) => r._tag).join("+") : (Cause.isInterruptedOnly(x.cause) ? "Interrupt" : "Failure"))

type Style = "uninterruptible" | "mask"
const run = (style: Style, cancel: boolean, callerMasked: boolean) =>
  Effect.gen(function*() {
    const q = yield* Queue.unbounded()
    yield* Queue.offer(q, "m")
    const committed = yield* Deferred.make()
    const events: Array<string> = []
    const body = Effect.gen(function*() {
      const value = yield* Queue.take(q)
      events.push("consumed")
      yield* Deferred.succeed(committed, undefined)
      yield* settle
      events.push("body-result")
      return value
    })
    const protectedOp = style === "uninterruptible"
      ? Effect.uninterruptible(body)
      : Effect.uninterruptibleMask(() => body)
    const op = Effect.onExit(protectedOp, (x: any) => Effect.sync(() => events.push(`operation-exit:${showExit(x)}`)))
    const caller = Effect.gen(function*() {
      const value = yield* op
      events.push(`caller-continued:${value}`)
      return value
    })
    const target = yield* fork(callerMasked ? Effect.uninterruptible(caller) : caller)
    yield* Deferred.await(committed)
    if (cancel) yield* fork(Fiber.interrupt(target))
    const exit = yield* Fiber.await(target)
    const left = yield* Queue.size(q)
    return { style, cancel, callerMasked, events, fiberExit: showExit(exit), left }
  })

// The control before consumption: the take waits on an empty queue under a restored mask.
const beforeConsumption = Effect.gen(function*() {
  const q = yield* Queue.unbounded()
  const events: Array<string> = []
  const target = yield* fork(Effect.uninterruptibleMask((restore: any) =>
    restore(Effect.gen(function*() {
      const value = yield* Queue.take(q)
      events.push(`caller-continued:${value}`)
      return value
    }))
  ))
  yield* settle
  yield* Fiber.interrupt(target)
  const exit = yield* Fiber.await(target)
  yield* Queue.offer(q, "kept")
  yield* settle
  const left = yield* Queue.size(q)
  return { events, fiberExit: showExit(exit), left }
})

const main = Effect.gen(function*() {
  const out: Record<string, unknown> = { effect: version }
  out.noCancel = yield* run("uninterruptible", false, false)
  out.cancelInUninterruptible = yield* run("uninterruptible", true, false)
  out.cancelInMask = yield* run("mask", true, false)
  out.cancelCallerMasked = yield* run("mask", true, true)
  out.cancelBeforeConsumption = yield* beforeConsumption
  return out
})

Effect.runPromise(main).then((r: unknown) => console.log(JSON.stringify(r)))
