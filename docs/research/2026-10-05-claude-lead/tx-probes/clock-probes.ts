// Clock probes over one Effect build (2026-10-05). Finite host runs, not proofs.
//
// Run: EFFECT_DIR=<an effect package directory> bun run clock-probes.ts
// Effect 4 only: the test clock is loaded from dist/testing/TestClock.js.
import { existsSync, readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const { Effect, Fiber, Clock, Duration } = await import(`${dir}/dist/index.js`)
const TestClock = await import(`${dir}/dist/testing/TestClock.js`)
const fork = Effect.forkChild
const settle = Effect.gen(function*() {
  for (let i = 0; i < 8; i++) yield* Effect.yieldNow
})
const big = (n: bigint) => n.toString()

// C1. What a Duration holds. Every finite duration is a whole count of nanoseconds.
const c1 = {
  halfMilli: big(Duration.toNanosUnsafe(Duration.millis(0.5))),
  oneNano: big(Duration.toNanosUnsafe(Duration.nanos(1n))),
  third: big(Duration.toNanosUnsafe(Duration.millis(1 / 3))),
  nanosAsMillis: Duration.toMillis(Duration.nanos(300_000n))
}

// C2. The live clock: three readings, and the least gap the monotonic reading shows.
const c2 = Effect.gen(function*() {
  const millis = yield* Clock.currentTimeMillis
  const nanos = yield* Clock.currentTimeNanos
  const gaps: Array<bigint> = []
  let last = yield* Clock.monotonicTimeNanos
  for (let i = 0; i < 20000; i++) {
    const now = yield* Clock.monotonicTimeNanos
    if (now !== last) gaps.push(now - last)
    last = now
  }
  gaps.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0))
  return {
    millisIsInteger: Number.isInteger(millis),
    nanosDigits: big(nanos).length,
    leastMonotonicGapNanos: gaps.length > 0 ? big(gaps[0]) : "none"
  }
})

// C3. The live clock: how long a sleep of 100 microseconds takes, in nanoseconds.
const c3 = Effect.gen(function*() {
  const took: Array<number> = []
  for (let i = 0; i < 5; i++) {
    const t0 = yield* Clock.monotonicTimeNanos
    yield* Effect.sleep(Duration.micros(100n))
    const t1 = yield* Clock.monotonicTimeNanos
    took.push(Number(t1 - t0))
  }
  return { asked: 100_000, tookNanos: took }
})

// C4. The test clock. A fiber sleeps 300 000 ns and reads the three registers when it wakes.
// The main fiber then adjusts by one millisecond.
const c4 = (startMillis: number) =>
  Effect.gen(function*() {
    if (startMillis > 0) yield* TestClock.setTime(startMillis)
    let woke: unknown = "asleep"
    const f = yield* fork(Effect.gen(function*() {
      yield* Effect.sleep(Duration.nanos(300_000n))
      woke = {
        millis: yield* Clock.currentTimeMillis,
        wallNanos: big(yield* Clock.currentTimeNanos),
        monotonicNanos: big(yield* Clock.monotonicTimeNanos)
      }
    }))
    yield* settle
    const beforeAdjust = woke
    yield* TestClock.adjust(Duration.millis(1))
    yield* settle
    const out = {
      startMillis,
      beforeAdjust,
      atWake: woke,
      atEnd: {
        millis: yield* Clock.currentTimeMillis,
        wallNanos: big(yield* Clock.currentTimeNanos),
        monotonicNanos: big(yield* Clock.monotonicTimeNanos)
      }
    }
    yield* Fiber.interrupt(f)
    return out
  }).pipe(Effect.provide(TestClock.layer()))

// C5. The test clock. Two fibers sleep 100 ns and 200 ns. The main fiber adjusts by 150 ns.
// An exact clock wakes the first and not the second.
const c5 = (startMillis: number) =>
  Effect.gen(function*() {
    if (startMillis > 0) yield* TestClock.setTime(startMillis)
    const woke: Array<string> = []
    const a = yield* fork(Effect.sleep(Duration.nanos(100n)).pipe(Effect.andThen(Effect.sync(() => woke.push("100ns")))))
    const b = yield* fork(Effect.sleep(Duration.nanos(200n)).pipe(Effect.andThen(Effect.sync(() => woke.push("200ns")))))
    yield* settle
    const beforeAdjust = [...woke]
    yield* TestClock.adjust(Duration.nanos(150n))
    yield* settle
    const out = { startMillis, beforeAdjust, afterAdjust150ns: [...woke] }
    yield* Fiber.interrupt(a)
    yield* Fiber.interrupt(b)
    return out
  }).pipe(Effect.provide(TestClock.layer()))

const main = Effect.gen(function*() {
  const out: Record<string, unknown> = { effect: version }
  out.c1_durations = c1
  out.c2_liveReadings = yield* c2
  out.c3_liveSleep100us = yield* c3
  out.c4_testClockRegisters = [yield* c4(0), yield* c4(1_700_000_000_000)]
  out.c5_testClockSubMicro = [yield* c5(0), yield* c5(1_700_000_000_000)]
  return out
})

Effect.runPromise(main).then((r: unknown) => console.log(JSON.stringify(r)))
