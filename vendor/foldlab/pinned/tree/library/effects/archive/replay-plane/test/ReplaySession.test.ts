import { expect, it } from "@effect/vitest"
import {
  Clock,
  Context,
  Deferred,
  Effect,
  Encoding,
  Fiber,
  Layer,
  Random,
  Ref,
  Schedule,
  Schema,
} from "effect"
import {
  ContentId,
  StoreFailure,
  type CasError,
} from "../src/cas/Node.ts"
import {
  layerMemory,
  type CasAddress,
} from "../src/cas/Store.ts"
import type { ServiceDescriptions } from "../src/replay/Operation.ts"
import {
  layerReplay,
  Replay,
  session,
} from "../src/replay/Replay.ts"
import {
  DoubleWrap,
  replayable,
  type Live,
} from "../src/replay/ServiceAdapter.ts"
import {
  decodeWitness,
  StoredWitness,
} from "../src/internal/storage.ts"
import {
  HistoryKindTag,
  trackingAddress,
  WitnessKindTag,
} from "./fixtures/address.ts"

class QuoteUnavailable extends Schema.TaggedError<QuoteUnavailable>()(
  "Rates/QuoteUnavailable",
  { symbol: Schema.String },
) {}

interface RatesShape {
  readonly quote: (
    symbol: string,
  ) => Effect.Effect<number, QuoteUnavailable>
}

class Rates extends Context.Service<Rates, RatesShape>()(
  "test/effect-replay/Rates",
) {}

const RatesDescriptions = {
  quote: {
    id: "test/Rates/quote",
    revision: 0,
    request: Schema.String,
    success: Schema.Number,
    failure: QuoteUnavailable,
    leafReplay: "substitutable",
  },
} satisfies ServiceDescriptions<RatesShape>

interface StringRatesShape {
  readonly quote: (
    symbol: string,
  ) => Effect.Effect<string, QuoteUnavailable>
}

class StringRates extends Context.Service<StringRates, StringRatesShape>()(
  "test/effect-replay/StringRates",
) {}

const StringRatesDescriptions = {
  quote: {
    id: "test/Rates/quote",
    revision: 0,
    request: Schema.String,
    success: Schema.String,
    failure: QuoteUnavailable,
    leafReplay: "substitutable",
  },
} satisfies ServiceDescriptions<StringRatesShape>

const makeFake = () => {
  let invocations = 0
  const service = Rates.of({
    quote: Effect.fn("Rates.quote")((symbol: string) =>
      Effect.suspend(() => {
        invocations += 1
        return symbol === "missing"
          ? Effect.fail(new QuoteUnavailable({ symbol }))
          : Effect.succeed(symbol.length)
      })),
  })
  return { service, invocations: () => invocations }
}

const callerProgram: Effect.Effect<
  readonly [number, number],
  QuoteUnavailable,
  Rates
> =
  Rates.use((rates) =>
    Effect.gen(function* () {
      const recovered = yield* rates.quote("missing").pipe(
        Effect.catchTag("Rates/QuoteUnavailable", () => Effect.succeed(-1)),
      )
      const quoted = yield* rates.quote("EUR")
      return [recovered, quoted] as const
    }))


it.effect("caller-supplied execution identity is persisted verbatim", () => {
  const tracked = trackingAddress()
  return Effect.gen(function* () {
    yield* session(Effect.void, {
      mode: "record",
      executionId: "worker-7/attempt-42",
    })
    yield* session(Effect.void, { mode: "record" })

    const identities = tracked.witnesses().map((witness) => witness.executionId)
    expect(identities[0]).toBe("worker-7/attempt-42")
    expect(identities[1]).toMatch(/^execution-[1-9][0-9]*$/)
  }).pipe(Effect.provide(runtimeLayer(tracked.address)))
})

const runtimeLayer = (address: CasAddress) =>
  layerReplay.pipe(Layer.provide(layerMemory(address)))

type Equal<Left, Right> = [Left] extends [Right]
  ? [Right] extends [Left] ? true : false
  : false

type Requirements<L extends Layer.Any> = Layer.Services<L>

it.effect("CTX-001 runs one caller program through live, record, and replay layers", () => {
  const tracked = trackingAddress()
  const fake = makeFake()
  const kit = replayable(Rates, RatesDescriptions)

  const replayRequiresNoLive: Equal<Requirements<typeof kit.replay>, Replay> = true
  const recordRequiresLive: Equal<
    Requirements<typeof kit.record>,
    Replay | Live<Rates>
  > = true

  return Effect.gen(function* () {
    expect(replayRequiresNoLive).toBe(true)
    expect(recordRequiresLive).toBe(true)

    const live = yield* callerProgram.pipe(
      Effect.provideService(Rates, fake.service),
    )
    expect(live).toEqual([-1, 3])
    expect(fake.invocations()).toBe(2)

    const recorded = yield* session(
      callerProgram.pipe(
        Effect.provide(kit.record),
        Effect.provideService(kit.live, fake.service),
      ),
      { mode: "record" },
    )
    expect(recorded.outcome).toEqual({
      _tag: "Completed",
      terminal: { _tag: "Succeeded", value: [-1, 3] },
    })
    expect(fake.invocations()).toBe(4)

    const history = tracked.latestHistory()
    expect(history).toBeDefined()
    if (history === undefined) return yield* Effect.die("missing recorded history root")

    const replayed = yield* session(
      callerProgram.pipe(Effect.provide(kit.replay)),
      { mode: "replay", history },
    )
    expect(replayed.outcome).toEqual(recorded.outcome)
    expect(fake.invocations()).toBe(4)
  }).pipe(Effect.provide(runtimeLayer(tracked.address)))
})

it.effect("overlapping record invocations are refused as DelegationOutstanding", () => {
  // SES-003: record-mode delegation is exclusive. A second invocation
  // while one delegation is in flight is a typed session rejection —
  // never a completion-ordered history. Sound concurrent recording needs
  // event identity and causality, reserved as its own milestone.
  const tracked = trackingAddress()
  const kit = replayable(Rates, RatesDescriptions)

  return Effect.gen(function* () {
    const parked = yield* Deferred.make<void>()
    const live = Rates.of({
      quote: () => Deferred.await(parked).pipe(Effect.as(3)),
    })
    const concurrent = Rates.use((rates) =>
      Effect.all([
        rates.quote("EUR"),
        rates.quote("EUR"),
      ], { concurrency: 2 }))

    const recorded = yield* session(concurrent.pipe(
      Effect.provide(kit.record),
      Effect.provideService(kit.live, live),
    ), { mode: "record" })
    expect(recorded.outcome).toMatchObject({
      _tag: "Rejected",
      category: "DelegationOutstanding",
      at: 0,
    })
    // Nothing appended: the refusal fired before any occurrence existed,
    // and the persisted witness reports the rejection.
    expect(recorded.history).toBeUndefined()
    expect(tracked.witnessedOutcomes()).toEqual([
      { _tag: "Rejected", category: "DelegationOutstanding", at: 0 },
    ])
  }).pipe(Effect.provide(runtimeLayer(tracked.address)))
})

it.effect("defects and caller interruption persist aborted-attempt witnesses", () => {
  const tracked = trackingAddress()
  const kit = replayable(Rates, RatesDescriptions, makeFake().service)

  return Effect.gen(function* () {
    const defectExit = yield* session(
      Rates.use((rates) => rates.quote("EUR")).pipe(
        Effect.andThen(Effect.die("handler-after-record defect")),
        Effect.provide(kit.record),
      ),
      { mode: "record" },
    ).pipe(Effect.exit)
    expect(defectExit._tag).toBe("Failure")

    const parked = yield* Deferred.make<void>()
    const interruptible = session(
      Rates.use((rates) => rates.quote("USD")).pipe(
        Effect.tap(() => Deferred.succeed(parked, undefined)),
        Effect.andThen(Effect.never),
        Effect.provide(kit.record),
      ),
      { mode: "record" },
    )
    const fiber = yield* interruptible.pipe(Effect.forkChild)
    yield* Deferred.await(parked)
    yield* Fiber.interrupt(fiber)
    const interrupted = yield* Fiber.await(fiber)
    expect(interrupted._tag).toBe("Failure")
    expect(tracked.witnessedOutcomes()).toEqual([
      { _tag: "Aborted", reason: "Defect" },
      { _tag: "Aborted", reason: "Interrupted" },
    ])
  }).pipe(Effect.provide(runtimeLayer(tracked.address)))
})

interface HostValueShape {
  readonly value: (kind: string) => Effect.Effect<unknown>
}

class HostValue extends Context.Service<HostValue, HostValueShape>()(
  "test/effect-replay/HostValue",
) {}

const HostValueDescriptions = {
  value: {
    id: "test/HostValue/value",
    revision: 0,
    request: Schema.String,
    success: Schema.Unknown,
    failure: Schema.Never,
    leafReplay: "substitutable",
  },
} satisfies ServiceDescriptions<HostValueShape>

it.effect("recording rejects Date, Map, and Set values before a replay artifact is admitted", () => {
  const tracked = trackingAddress()
  const values = new Map<string, unknown>([
    ["Date", new Date(0)],
    ["Map", new Map([["key", "value"]])],
    ["Set", new Set(["value"])],
  ])
  const kit = replayable(HostValue, HostValueDescriptions, HostValue.of({
    value: (kind) => Effect.succeed(values.get(kind)),
  }))

  return Effect.gen(function* () {
    for (const kind of values.keys()) {
      const failure = yield* session(
        HostValue.use((service) => service.value(kind)).pipe(Effect.provide(kit.record)),
        { mode: "record" },
      ).pipe(Effect.flip)
      expect(failure).toMatchObject({
        _tag: "CasError/StoreFailure",
        reason: expect.stringContaining("plain prototype"),
      })
    }
    expect(tracked.latestHistory()).toBeUndefined()
  }).pipe(Effect.provide(runtimeLayer(tracked.address)))
})

it.effect("RPL-002 and RPL-004 reject mismatch without a live fallback", () => {
  const tracked = trackingAddress()
  const fake = makeFake()
  const kit = replayable(Rates, RatesDescriptions, fake.service)

  const byValueRecordNeedsOnlyReplay: Equal<
    Requirements<typeof kit.record>,
    Replay
  > = true

  return Effect.gen(function* () {
    expect(byValueRecordNeedsOnlyReplay).toBe(true)

    yield* session(
      Rates.use((rates) => rates.quote("EUR")).pipe(Effect.provide(kit.record)),
      { mode: "record" },
    )
    const history = tracked.latestHistory()
    if (history === undefined) return yield* Effect.die("missing recorded history root")
    expect(fake.invocations()).toBe(1)

    const rejected = yield* session(
      Rates.use((rates) => rates.quote("USD")).pipe(Effect.provide(kit.replay)),
      { mode: "replay", history },
    )
    expect(rejected.outcome).toEqual({
      _tag: "Rejected",
      category: "RequestMismatch",
      at: 0,
    })
    expect(fake.invocations()).toBe(1)
  }).pipe(Effect.provide(runtimeLayer(tracked.address)))
})

it.effect("RPL-004 rejects an inadmissible recorded outcome at the frozen cursor", () => {
  const tracked = trackingAddress()
  const fake = makeFake()
  const numberKit = replayable(Rates, RatesDescriptions, fake.service)
  const stringKit = replayable(StringRates, StringRatesDescriptions)

  return Effect.gen(function* () {
    yield* session(
      Rates.use((rates) => rates.quote("EUR")).pipe(Effect.provide(numberKit.record)),
      { mode: "record" },
    )
    const history = tracked.latestHistory()
    if (history === undefined) return yield* Effect.die("missing recorded history root")

    const rejected = yield* session(
      StringRates.use((rates) => rates.quote("EUR")).pipe(
        Effect.provide(stringKit.replay),
      ),
      { mode: "replay", history },
    )
    expect(rejected.outcome).toEqual({
      _tag: "Rejected",
      category: "OutcomeInadmissible",
      at: 0,
    })
    expect(fake.invocations()).toBe(1)
  }).pipe(Effect.provide(runtimeLayer(tracked.address)))
})

it.effect("CAS load miss remains ContentNotFound at the session boundary", () => {
  const tracked = trackingAddress()
  const absent = ContentId.make("ff".repeat(32))
  return session(Effect.void, { mode: "replay", history: absent }).pipe(
    Effect.match({
      onFailure: (error) => {
        expect(error._tag).toBe("CasError/ContentNotFound")
        return error._tag
      },
      onSuccess: () => "unexpected success",
    }),
    Effect.map((tag) => expect(tag).toBe("CasError/ContentNotFound")),
    Effect.provide(runtimeLayer(tracked.address)),
  )
})

it.effect("SES-001 transports append failure past the wrapped error union", () => {
  const fake = makeFake()
  const kit = replayable(Rates, RatesDescriptions, fake.service)
  const failHistory: CasAddress = {
    digest: (bytes) => bytes[1] === HistoryKindTag
      ? Effect.fail(new StoreFailure({ reason: "injected history append failure" }))
      : Effect.succeed(ContentId.make("01".repeat(32))),
  }

  const program: Effect.Effect<number, QuoteUnavailable, Rates> =
    Rates.use((rates) => rates.quote("EUR"))

  return session(program.pipe(Effect.provide(kit.record)), { mode: "record" }).pipe(
    Effect.match({
      onFailure: (error: CasError) => {
        expect(error).toEqual(new StoreFailure({
          reason: "injected history append failure",
        }))
        return error._tag
      },
      onSuccess: () => "unexpected success",
    }),
    Effect.map((tag) => {
      expect(tag).toBe("CasError/StoreFailure")
      expect(fake.invocations()).toBe(1)
    }),
    Effect.provide(runtimeLayer(failHistory)),
  )
})

it.effect("CTX-001 rejects a branded wrapper supplied as the live role", () => {
  const tracked = trackingAddress()
  const kit = replayable(Rates, RatesDescriptions)
  return Effect.gen(function* () {
    const wrapped = yield* Rates.pipe(Effect.provide(kit.replay))
    const second = replayable(Rates, RatesDescriptions, wrapped)
    const result = yield* Rates.pipe(
      Effect.provide(second.record),
      Effect.match({
        onFailure: (error) => error,
        onSuccess: () => undefined,
      }),
    )
    expect(result).toEqual(new DoubleWrap({ service: Rates.key }))
  }).pipe(Effect.provide(runtimeLayer(tracked.address)))
})

it.effect("CTX-002 surfaces Clock and Random defaults as flat Violated outcomes", () => {
  const tracked = trackingAddress()
  return Effect.gen(function* () {
    const clock = yield* session(Clock.currentTimeMillis, { mode: "replay" })
    expect(clock.outcome).toEqual({ _tag: "Violated", service: "Clock" })

    const random = yield* session(Random.next, { mode: "replay" })
    expect(random.outcome).toEqual({ _tag: "Violated", service: "Random" })
  }).pipe(Effect.provide(runtimeLayer(tracked.address)))
})

it.effect("CTX-002 keeps direct Date.now as a permanent raw-host counterexample", () => {
  const tracked = trackingAddress()
  return Effect.gen(function* () {
    const outcome = yield* session(Effect.sync(() => Date.now()), { mode: "replay" })
    expect(outcome.outcome._tag).toBe("Completed")
    if (outcome.outcome._tag === "Completed") {
      expect(outcome.outcome.terminal._tag).toBe("Succeeded")
      if (outcome.outcome.terminal._tag === "Succeeded") {
        expect(typeof outcome.outcome.terminal.value).toBe("number")
      }
    }
  }).pipe(Effect.provide(runtimeLayer(tracked.address)))
})

it.effect("CTX-002 catches jittered retry through Effect default services", () => {
  const tracked = trackingAddress()
  const jittered = Effect.fail("retry").pipe(
    Effect.retry(Schedule.recurs(1).pipe(Schedule.jittered)),
  )
  return Effect.gen(function* () {
    const outcome = yield* session(jittered, { mode: "replay" })
    expect(outcome.outcome).toEqual({ _tag: "Violated", service: "Clock" })
  }).pipe(Effect.provide(runtimeLayer(tracked.address)))
})
