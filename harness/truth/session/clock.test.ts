import { describe, expect, test } from "bun:test"
import { Clock, Duration, Effect } from "effect"
import { TestClock } from "effect/testing"
import { clockMillis, clockNumber, durationMillis, ProfileRefusal, Rc112ClockBoundary } from "./clock.ts"

describe("exact clock and numeric target boundary", () => {
  test("decimal round trips beyond both numeric target ranges", () => {
    for (const text of ["0", "9007199254740993", "4611686018427387904", "123456789012345678901234567890"])
      expect(clockMillis(text).toString()).toBe(text)
    const a = clockMillis("4611686018427387904")
    expect((a + 1n).toString()).toBe("4611686018427387905")
    expect(a < a + 1n).toBe(true)
  })
  test("noncanonical transport and numeric overflow refuse", () => {
    for (const value of ["", "00", "01", "+1", "-1", " 1", "1 ", "1e3", "0x10", 1])
      expect(() => clockMillis(value)).toThrow()
    expect(() => clockNumber(9007199254740992n)).toThrow(ProfileRefusal)
    expect(clockNumber(17n)).toBe(17)
  })
  test("nanoseconds are checked exactly before any numeric conversion", () => {
    expect(() => durationMillis(Duration.nanos(1000000000000000001n))).toThrow(ProfileRefusal)
    expect(durationMillis(Duration.nanos(1000000000000000000n))).toBe(1000000000000n)
  })
  test("the provided service exposes only the pinned Clock readers and checked sleep", async () => {
    const clock = await Rc112ClockBoundary.make()
    try {
      const fields = await Effect.runPromise(clock.provide(Clock.clockWith(service =>
        Effect.succeed(Object.keys(service).sort()))))
      expect(fields).toEqual([
        "currentTimeMillis", "currentTimeMillisUnsafe", "currentTimeNanos", "currentTimeNanosUnsafe",
        "monotonicTimeNanos", "monotonicTimeNanosUnsafe", "sleep"
      ])
      await clock.advance("17")
      const times = await Effect.runPromise(clock.provide(Clock.clockWith(service => Effect.gen(function* () {
        return [
          service.currentTimeMillisUnsafe(), yield* service.currentTimeMillis,
          service.currentTimeNanosUnsafe(), yield* service.currentTimeNanos,
          service.monotonicTimeNanosUnsafe(), yield* service.monotonicTimeNanos
        ]
      }))))
      expect(times).toEqual([17, 17, 17000000n, 17000000n, 17000000n, 17000000n])
    } finally {
      await clock.dispose()
    }
  })
  test("in-program TestClock mutation is unsupported and cannot bypass the numeric boundary", async () => {
    for (const mutation of [TestClock.adjust(9007199254740992), TestClock.setTime(9007199254740992)]) {
      const clock = await Rc112ClockBoundary.make()
      try {
        await expect(Effect.runPromise(clock.provide(mutation))).rejects.toThrow("not a function")
        expect(clock.now()).toBe(0n)
      } finally {
        await clock.dispose()
      }
    }
  })
  test("stock TestClock rejects an overflowing adjustment before mutation", async () => {
    const clock = await Rc112ClockBoundary.make()
    await clock.advance("9007199254740991")
    const before = clock.now()
    await expect(clock.advance("1")).rejects.toBeInstanceOf(ProfileRefusal)
    expect(clock.now()).toBe(before)
    await clock.dispose()
  })
  test("stock TestClock refuses an overflowing deadline without a program failure", async () => {
    const clock = await Rc112ClockBoundary.make()
    await clock.advance("9007199254740991")
    let completed = false
    const fiber = Effect.runFork(clock.provide(Effect.sleep(1)))
    fiber.addObserver(() => { completed = true })
    await new Promise<void>(resolve => setTimeout(resolve, 0))
    expect(clock.refusal).toBeInstanceOf(ProfileRefusal)
    expect(clock.now()).toBe(9007199254740991n)
    expect(completed).toBe(false)
    expect(() => clock.check()).toThrow(ProfileRefusal)
    fiber.interruptUnsafe()
    await clock.dispose()
  })
  test("refusal takes precedence even after a concurrent root completes", async () => {
    const clock = await Rc112ClockBoundary.make()
    await clock.advance("9007199254740991")
    const completed = await Effect.runPromise(clock.provide(
      Effect.raceFirst(Effect.sleep(1), Effect.succeed(true))))
    expect(completed).toBe(true)
    expect(() => clock.check()).toThrow(ProfileRefusal)
    await clock.dispose()
  })
})
