/** Fourteen Pull cases and the five foundation boundaries, using pinned rc.112 directly.
 * The mixed-cause, cursor, demand and queue vectors extend the retained 2026-09-09 probes.
 * Expected values are literals or independently constructed Exit/Cause values. */
import { describe, expect, test } from "bun:test"
import { deepStrictEqual } from "node:assert"
import * as Cause from "../../vendor/effect-4.0.0-rc.112/src/Cause.ts"
import * as Channel from "../../vendor/effect-4.0.0-rc.112/src/Channel.ts"
import * as Effect from "../../vendor/effect-4.0.0-rc.112/src/Effect.ts"
import * as Exit from "../../vendor/effect-4.0.0-rc.112/src/Exit.ts"
import * as Fiber from "../../vendor/effect-4.0.0-rc.112/src/Fiber.ts"
import * as Pull from "../../vendor/effect-4.0.0-rc.112/src/Pull.ts"
import * as Queue from "../../vendor/effect-4.0.0-rc.112/src/Queue.ts"
import * as Result from "../../vendor/effect-4.0.0-rc.112/src/Result.ts"
import * as Stream from "../../vendor/effect-4.0.0-rc.112/src/Stream.ts"

const done7 = Cause.makeFailReason(Cause.Done(7))
const bad = Cause.makeFailReason("bad")
const broken = Cause.makeDieReason("broken")
const interrupt = Cause.makeInterruptReason(3)
const cause = (...reasons: Cause.Reason<string | Cause.Done<number>>[]) => Cause.fromReasons(reasons)

describe("Pull:14 — Pull.ts:236-295,389-420", () => {
  const doneCases = [
    ["done retains payload", cause(done7), Cause.Done(7)],
    ["done plus interrupt is clean end", cause(done7, interrupt), Cause.Done(7)],
    ["first done payload wins", cause(done7, Cause.makeFailReason(Cause.Done(8))), Cause.Done(7)]
  ] as const
  for (const [name, input, value] of doneCases)
    test(name, () => deepStrictEqual(Pull.filterDone(input), Result.succeed(value)))
  const failureCases = [
    ["done cannot hide failure", cause(done7, bad), cause(bad)],
    ["done cannot hide defect", cause(done7, broken), cause(broken)],
    ["interrupt alone stays interruption", cause(interrupt), cause(interrupt)],
    ["failure alone stays failure", cause(bad), cause(bad)],
    ["defect alone stays defect", cause(broken), cause(broken)],
    ["empty cause is not end", cause(), cause()],
    ["mixed failure retains interruption", cause(done7, bad, interrupt), cause(bad, interrupt)]
  ] as const
  for (const [name, input, expected] of failureCases)
    test(name, () => deepStrictEqual(Pull.filterDone(input), Result.fail(expected)))
  test("cleanup receives successful done payload", () =>
    expect(Pull.doneExitFromCause(cause(done7))).toEqual(Exit.succeed(7)))
  test("cleanup retains real failure", () =>
    expect(Pull.doneExitFromCause(cause(done7, bad))).toEqual(Exit.fail("bad")))
  test("match success retains ordinary output", () =>
    expect(Effect.runSync(Pull.matchEffect(Effect.succeed(5), {
      onSuccess: n => Effect.succeed(["chunk", n]),
      onFailure: () => Effect.succeed(["error"]),
      onDone: () => Effect.succeed(["done"])
    }))).toEqual(["chunk", 5]))
  test("match failure cannot select done", () =>
    expect(Effect.runSync(Pull.matchEffect(Effect.fail("bad"), {
      onSuccess: () => Effect.succeed("chunk"),
      onFailure: () => Effect.succeed("error"),
      onDone: () => Effect.succeed("done")
    }))).toBe("error"))
})

describe("Five foundation boundaries", () => {
  test("S1: completion is separate from finalizer failure — Pull.ts:277-295,389", () => {
    expect(Pull.doneExitFromCause(cause(done7, broken))).toEqual(Exit.die("broken"))
    expect(Pull.isDoneCause(cause(done7, broken))).toBe(true)
    expect(Result.isSuccess(Pull.filterDone(cause(done7, broken)))).toBe(false)
  })

  test("S2: independent openings and serialized pulls — Channel.ts:734,11412-11456", async () => {
    const result = Effect.runSync(Effect.scoped(Effect.gen(function* () {
      const description = Stream.fromArrays([1], [2])
      const a = yield* Stream.toPull(description), b = yield* Stream.toPull(description)
      return [yield* a, yield* a, yield* b]
    })))
    expect(result).toEqual([[1], [2], [1]])
    const concurrent = (serialized: boolean) => Effect.runPromise(Effect.scoped(Effect.gen(function* () {
      const channel = Channel.fromPull(Effect.sync(() => {
        let index = 0
        return Effect.gen(function* () {
          const read = index
          yield* Effect.yieldNow
          index = read + 1
          return read
        })
      }))
      const scope = yield* Effect.scope
      const pull = yield* (serialized ? Channel.toPull(channel) : Channel.toPullScoped(channel, scope))
      return yield* Effect.all([pull, pull], { concurrency: 2 })
    })))
    expect(await concurrent(true)).toEqual([0, 1])
    expect(await concurrent(false)).toEqual([0, 0])
  })

  test("S3: parking retains state; explicit disposal cleans once — Effect.ts:1667,12815,12928", async () => {
    const events: string[] = []
    let resume: ((effect: Effect.Effect<number>) => void) | undefined
    const fiber = Effect.runFork(Effect.scoped(Effect.gen(function* () {
      yield* Effect.acquireRelease(Effect.sync(() => events.push("open")), () => Effect.sync(() => events.push("close")))
      yield* Effect.sync(() => events.push("write"))
      return yield* Effect.callback<number>(answer => { resume = answer })
    })))
    expect(events).toEqual(["open", "write"])
    expect(resume).toBeDefined()
    resume!(Effect.succeed(7))
    expect(await Effect.runPromise(Fiber.join(fiber))).toBe(7)
    expect(events).toEqual(["open", "write", "close"])
    fiber.interruptUnsafe()
    expect(events).toEqual(["open", "write", "close"])
    const cancelledEvents: string[] = []
    const cancelled = Effect.runFork(Effect.scoped(Effect.gen(function* () {
      yield* Effect.acquireRelease(Effect.void, () => Effect.sync(() => cancelledEvents.push("close")))
      yield* Effect.sync(() => cancelledEvents.push("write"))
      yield* Effect.never
    })))
    expect(cancelledEvents).toEqual(["write"])
    cancelled.interruptUnsafe()
    await Effect.runPromiseExit(Fiber.join(cancelled))
    cancelled.interruptUnsafe()
    expect(cancelledEvents).toEqual(["write", "close"])
    let finishCleanup: ((effect: Effect.Effect<void>) => void) | undefined
    let settled = false
    const awaitingCleanup = Effect.runFork(Effect.scoped(Effect.acquireRelease(Effect.void,
      () => Effect.callback<void>(answer => { finishCleanup = answer }))))
    awaitingCleanup.addObserver(() => { settled = true })
    expect(finishCleanup).toBeDefined()
    expect(settled).toBe(false)
    finishCleanup!(Effect.void)
    await Effect.runPromise(Fiber.join(awaitingCleanup))
    expect(settled).toBe(true)
  })

  test("S4: nonempty chunks and demand — Stream.ts:1045,1097,11626", () => {
    const observed = Effect.runSync(Effect.scoped(Effect.gen(function* () {
      const pull = yield* Stream.toPull(Stream.fromArrays([], [1], [], [2, 3], []))
      const one = yield* pull, two = yield* pull, terminal = yield* Effect.exit(pull)
      if (Exit.isSuccess(terminal)) throw Error("expected terminal pull")
      return [one, two, Pull.doneExitFromCause(terminal.cause)]
    })))
    expect(observed).toEqual([[1], [2, 3], Exit.void])
    const take = (n: number) => {
      let advanced = 0
      const source = Stream.fromIterable({ [Symbol.iterator]: function* () { while (true) { advanced++; yield advanced } } }, { chunkSize: 3 })
      return { elements: Effect.runSync(Stream.runCollect(Stream.take(source, n))), advances: advanced }
    }
    expect(take(0)).toEqual({ elements: [], advances: 0 })
    expect(take(1)).toEqual({ elements: [1], advances: 3 })
    expect([[1, 2], [3]].flat()).toEqual([[1], [2, 3]].flat())
    expect([[1, 2], [3]]).not.toEqual([[1], [2, 3]])
  })

  test("S5: drain versus shutdown; full is not failure — Queue.ts:645,1000,1191", async () => {
    const end = Effect.runSync(Effect.gen(function* () {
      const q = yield* Queue.make<number, Cause.Done>()
      yield* Queue.offer(q, 1)
      yield* Queue.end(q)
      return [yield* Queue.take(q), yield* Effect.exit(Queue.take(q))]
    }))
    expect(end).toEqual([1, Exit.fail(Cause.Done())])
    const shutdown = Effect.runSync(Effect.gen(function* () {
      const q = yield* Queue.make<number>()
      yield* Queue.offer(q, 1)
      yield* Queue.shutdown(q)
      return yield* Effect.exit(Queue.take(q))
    }))
    expect(Exit.isFailure(shutdown) && Cause.hasInterrupts(shutdown.cause)).toBe(true)
    const dropping = Effect.runSync(Effect.gen(function* () {
      const q = yield* Queue.dropping<number>(1)
      return [yield* Queue.offer(q, 1), yield* Queue.offer(q, 2), yield* Queue.take(q)]
    }))
    expect(dropping).toEqual([true, false, 1])
    const q = Effect.runSync(Queue.bounded<number>(0))
    let accepted = false
    const producer = Effect.runFork(Effect.tap(Queue.offer(q, 9), () => Effect.sync(() => { accepted = true })))
    expect(accepted).toBe(false)
    expect(await Effect.runPromise(Queue.take(q))).toBe(9)
    expect(await Effect.runPromise(Fiber.join(producer))).toBe(true)
    expect(accepted).toBe(true)
  })
})
