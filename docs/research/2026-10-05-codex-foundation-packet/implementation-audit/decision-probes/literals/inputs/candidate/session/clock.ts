/** Exact clock transport and the rc.112 numeric boundary. The tape carries canonical
 * decimal strings; bigint arithmetic precedes every conversion. Refusal is a host outcome
 * recorded separately from a program's error/defect channel. */
import { Clock, Duration, Effect, Exit, Scope } from "effect"
import { TestClock } from "effect/testing"
import { ProtocolRefusal } from "./protocol.ts"

export class ProfileRefusal extends ProtocolRefusal {
  readonly _tag = "ProfileRefusal"
  constructor(message: string) { super("outsideProfile", message) }
}

export const clockMillis = (value: unknown): bigint => {
  if (typeof value !== "string" || !/^(0|[1-9][0-9]*)$/.test(value))
    throw new ProtocolRefusal("malformed", "clock milliseconds require canonical decimal text")
  return BigInt(value)
}

export const clockNumber = (value: bigint): number => {
  if (value < 0n || value > BigInt(Number.MAX_SAFE_INTEGER))
    throw new ProfileRefusal("clock milliseconds exceed the rc.112 number profile")
  return Number(value)
}

const naturalMillis = (value: number): bigint => {
  if (!Number.isSafeInteger(value) || value < 0 || Object.is(value, -0))
    throw new ProfileRefusal("clock duration is outside the rc.112 natural-number profile")
  return BigInt(value)
}

export const durationMillis = (duration: Duration.Duration): bigint => {
  switch (duration.value._tag) {
    case "Millis": return naturalMillis(duration.value.millis)
    case "Nanos": {
      const nanos = duration.value.nanos
      if (nanos < 0n || nanos % 1000000n !== 0n)
        throw new ProfileRefusal("clock duration requires an exact nonnegative millisecond")
      return nanos / 1000000n
    }
    default: throw new ProfileRefusal("infinite duration is not a clock deadline")
  }
}

/** The supplied stock TestClock is private: all adjustments and program sleeps go through
 * the checked service. A refused sleep parks until the host driver observes `refusal`;
 * it never becomes a catchable program failure, and it never reaches the timer table. */
export class Rc112ClockBoundary {
  refusal: ProfileRefusal | undefined
  private advancing: Promise<void> = Promise.resolve()
  private readonly service: Clock.Clock

  private constructor(private readonly clock: TestClock.TestClock, private readonly scope: Scope.Closeable) {
    this.service = {
      // rc.112 Clock.ts:51–153: readers and sleep only; no TestClock mutation controls.
      currentTimeMillisUnsafe: clock.currentTimeMillisUnsafe,
      currentTimeMillis: clock.currentTimeMillis,
      currentTimeNanosUnsafe: clock.currentTimeNanosUnsafe,
      currentTimeNanos: clock.currentTimeNanos,
      monotonicTimeNanosUnsafe: clock.monotonicTimeNanosUnsafe,
      monotonicTimeNanos: clock.monotonicTimeNanos,
      sleep: duration => Effect.suspend(() => {
        try {
          const millis = durationMillis(duration)
          clockNumber(this.now() + millis)
          return this.clock.sleep(Duration.millis(clockNumber(millis)))
        } catch (error) {
          if (!(error instanceof ProfileRefusal)) throw error
          this.refusal = error
          return Effect.never
        }
      })
    }
  }

  static async make(): Promise<Rc112ClockBoundary> {
    const scope = Scope.makeUnsafe()
    const clock = await Effect.runPromise(Effect.provideService(TestClock.make(), Scope.Scope, scope))
    return new Rc112ClockBoundary(clock, scope)
  }

  dispose(): Promise<void> { return Effect.runPromise(Scope.close(this.scope, Exit.succeed(undefined))) }

  now(): bigint { return naturalMillis(this.clock.currentTimeMillisUnsafe()) }

  check(): void { if (this.refusal) throw this.refusal }

  provide<A, E, R>(program: Effect.Effect<A, E, R>): Effect.Effect<A, E, R> {
    return Effect.provideService(program, Clock.Clock, this.service)
  }

  /** Check the whole addition before executing TestClock.adjust. Serialization ensures
   * two submitted adjustments cannot both validate against the same old timestamp.
   * Record an attempted decision only after this preflight and before it wakes any work.
   * A refusal in that work rejects the advance; it is not a successful host decision. */
  advance(decimal: string, beforeAdvance?: () => void): Promise<void> {
    const by = clockMillis(decimal)
    const operation = this.advancing.then(async () => {
      this.check()
      clockNumber(this.now() + by)
      const millis = clockNumber(by)
      beforeAdvance?.()
      await Effect.runPromise(this.clock.adjust(millis))
      this.check()
    })
    this.advancing = operation.catch(() => undefined)
    return operation
  }
}
