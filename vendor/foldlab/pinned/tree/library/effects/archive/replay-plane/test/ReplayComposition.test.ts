/**
 * M5 integration observations only. These fixtures exercise ordinary Effect
 * layer composition over the frozen runtime surface; they are not model
 * evidence and make no stability or canonicality claim about the internal
 * history and witness carriers inspected by this package-local suite.
 */
import { expect, it } from "@effect/vitest"
import { Context, Effect, Encoding, Layer, Schema } from "effect"
import { ContentId, type CasNodeInput } from "../src/cas/Node.ts"
import {
  CasStore,
  layerMemory,
  type CasStoreShape,
} from "../src/cas/Store.ts"
import type { ServiceDescriptions } from "../src/replay/Operation.ts"
import { layerReplay, Replay, session } from "../src/replay/Replay.ts"
import {
  decodeHistoryEntry,
  decodeWitness,
  StoredHistoryEntry,
  StoredWitness,
} from "../src/internal/storage.ts"
import { DoubleWrap, replayable } from "../src/replay/ServiceAdapter.ts"
import {
  HistoryKindTag,
  trackingAddress,
  WitnessKindTag,
  type TrackingAddress,
} from "./fixtures/address.ts"

class StockUnavailable extends Schema.TaggedError<StockUnavailable>()(
  "Composition/StockUnavailable",
  { sku: Schema.String },
) {}

interface StockShape {
  readonly reserve: (
    sku: string,
  ) => Effect.Effect<string, StockUnavailable>
}

class Stock extends Context.Service<Stock, StockShape>()(
  "test/effect-replay/composition/Stock",
) {}

const StockDescriptions = {
  reserve: {
    id: "test/Composition/Stock/reserve",
    revision: 0,
    request: Schema.String,
    success: Schema.String,
    failure: StockUnavailable,
    leafReplay: "substitutable",
  },
} satisfies ServiceDescriptions<StockShape>

class PriceUnavailable extends Schema.TaggedError<PriceUnavailable>()(
  "Composition/PriceUnavailable",
  { sku: Schema.String },
) {}

interface PricingShape {
  readonly quote: (
    sku: string,
  ) => Effect.Effect<number, PriceUnavailable>
}

class Pricing extends Context.Service<Pricing, PricingShape>()(
  "test/effect-replay/composition/Pricing",
) {}

const PricingDescriptions = {
  quote: {
    id: "test/Composition/Pricing/quote",
    revision: 0,
    request: Schema.String,
    success: Schema.Number,
    failure: PriceUnavailable,
    leafReplay: "substitutable",
  },
} satisfies ServiceDescriptions<PricingShape>

interface RepeatedResult {
  readonly reservations: readonly [string, string]
  readonly price: number
}

interface RecoveryResult {
  readonly reservation: string
  readonly price: number
}

type CompositionError = StockUnavailable | PriceUnavailable

interface OrchestrationShape {
  readonly repeat: (
    sku: string,
  ) => Effect.Effect<RepeatedResult, CompositionError>
  readonly nestedFailure: (
    sku: string,
  ) => Effect.Effect<RecoveryResult, CompositionError>
  readonly recover: (
    sku: string,
  ) => Effect.Effect<RecoveryResult, StockUnavailable>
  readonly route: (
    stockSku: string,
    pricingSku: string,
  ) => Effect.Effect<RepeatedResult, CompositionError>
}

class Orchestration extends Context.Service<Orchestration, OrchestrationShape>()(
  "test/effect-replay/composition/Orchestration",
) {}

/** Transparent orchestration: this service is never described or wrapped.
 * Its control flow re-executes while the two captured leaf services are the
 * record/replay wrappers supplied by the surrounding application layer. */
const orchestrationLayer: Layer.Layer<Orchestration, never, Stock | Pricing> =
  Layer.effect(
    Orchestration,
    Effect.gen(function* () {
      const stock = yield* Stock
      const pricing = yield* Pricing

      const repeat = Effect.fn("Composition.Orchestration.repeat")(function* (sku: string) {
        const first = yield* stock.reserve(sku)
        const price = yield* pricing.quote(sku)
        const second = yield* stock.reserve(sku)
        return { reservations: [first, second] as const, price }
      })

      const nestedFailure = Effect.fnUntraced(
        function* (sku: string) {
          const reservation = yield* stock.reserve(sku)
          const price = yield* pricing.quote("unpriced")
          return { reservation, price }
        },
      )

      const recover = Effect.fnUntraced(function* (sku: string) {
        const price = yield* pricing.quote("unpriced").pipe(
          Effect.catchTag("Composition/PriceUnavailable", () => Effect.succeed(0)),
        )
        const reservation = yield* stock.reserve(sku)
        return { reservation, price }
      })

      const route = Effect.fnUntraced(function* (
        stockSku: string,
        pricingSku: string,
      ) {
        const first = yield* stock.reserve(stockSku)
        const price = yield* pricing.quote(pricingSku)
        const second = yield* stock.reserve(stockSku)
        return { reservations: [first, second] as const, price }
      })

      return Orchestration.of({ repeat, nestedFailure, recover, route })
    }),
  )

interface CountedFake<S> {
  readonly service: S
  readonly calls: () => ReadonlyArray<string>
  readonly reset: () => void
}

const makeStockFake = (): CountedFake<StockShape> => {
  let calls: Array<string> = []
  return {
    service: Stock.of({
      reserve: Effect.fn("Composition.Stock.reserve")((sku: string) =>
        Effect.suspend(() => {
          calls.push(sku)
          return sku === "sold-out"
            ? Effect.fail(new StockUnavailable({ sku }))
            : Effect.succeed(`reserved:${sku}`)
        })),
    }),
    calls: () => calls,
    reset: () => {
      calls = []
    },
  }
}

const makePricingFake = (): CountedFake<PricingShape> => {
  let calls: Array<string> = []
  return {
    service: Pricing.of({
      quote: Effect.fn("Composition.Pricing.quote")((sku: string) =>
        Effect.suspend(() => {
          calls.push(sku)
          return sku === "unpriced"
            ? Effect.fail(new PriceUnavailable({ sku }))
            : Effect.succeed(sku.length * 10)
        })),
    }),
    calls: () => calls,
    reset: () => {
      calls = []
    },
  }
}


const requireValue = <A>(value: A | undefined, label: string): Effect.Effect<A> =>
  value === undefined ? Effect.die(`missing ${label}`) : Effect.succeed(value)

const observeHistory = (
  store: CasStoreShape,
  root: ContentId,
) =>
  Effect.gen(function* () {
    const reversed: Array<StoredHistoryEntry> = []
    let current: ContentId | undefined = root
    while (current !== undefined) {
      const node: CasNodeInput = yield* store.load(current)
      if (node.kind.tag !== HistoryKindTag) return yield* Effect.die("non-history node in history chain")
      const raw = yield* Effect.sync(() => decodeHistoryEntry(node.payload))
      reversed.push(yield* Schema.decodeUnknownEffect(StoredHistoryEntry)(raw))
      current = node.refs[0]?.id
    }
    reversed.reverse()
    return reversed
  })

const observeWitness = (
  store: CasStoreShape,
  id: ContentId,
) =>
  Effect.gen(function* () {
    const node = yield* store.load(id)
    if (node.kind.tag !== WitnessKindTag) return yield* Effect.die("expected witness node")
    const raw = yield* Effect.sync(() => decodeWitness(node.payload))
    return yield* Schema.decodeUnknownEffect(StoredWitness)(raw)
  })

interface CompositionFixture {
  readonly stock: CountedFake<StockShape>
  readonly pricing: CountedFake<PricingShape>
  readonly tracked: TrackingAddress
  readonly recordLayer: Layer.Layer<Orchestration, DoubleWrap, Replay>
  readonly replayLayer: Layer.Layer<Orchestration, never, Replay>
  readonly runtimeLayer: Layer.Layer<Replay | CasStore>
}

const makeFixture = (): CompositionFixture => {
  const stock = makeStockFake()
  const pricing = makePricingFake()
  const tracked = trackingAddress()

  const stockRecord = replayable(Stock, StockDescriptions, stock.service)
  const pricingRecord = replayable(Pricing, PricingDescriptions, pricing.service)
  const stockReplay = replayable(Stock, StockDescriptions)
  const pricingReplay = replayable(Pricing, PricingDescriptions)
  const recordLeaves = Layer.mergeAll(stockRecord.record, pricingRecord.record)
  const replayLeaves = Layer.mergeAll(stockReplay.replay, pricingReplay.replay)
  const recordLayer = orchestrationLayer.pipe(Layer.provide(recordLeaves))
  const replayLayer = orchestrationLayer.pipe(Layer.provide(replayLeaves))

  const storeLayer = layerMemory(tracked.address)
  const runtimeLayer = layerReplay.pipe(Layer.provideMerge(storeLayer))
  return {
    stock,
    pricing,
    tracked,
    recordLayer,
    replayLayer,
    runtimeLayer,
  }
}

/** The application graph is ordinary Layer composition: two independent
 * described leaf layers feed one transparent orchestration layer. */
const withRecordLayers = <A, E>(
  fixture: CompositionFixture,
  program: Effect.Effect<A, E, Orchestration>,
): Effect.Effect<A, E | DoubleWrap, Replay> =>
  program.pipe(Effect.provide(fixture.recordLayer))

const withReplayLayers = <A, E>(
  fixture: CompositionFixture,
  program: Effect.Effect<A, E, Orchestration>,
): Effect.Effect<A, E, Replay> =>
  program.pipe(Effect.provide(fixture.replayLayer))

const latestWitness = (fixture: CompositionFixture, label: string) =>
  requireValue(fixture.tracked.witnessIds().at(-1), `${label} witness`)

const resetLiveCounts = (fixture: CompositionFixture): void => {
  fixture.stock.reset()
  fixture.pricing.reset()
}

it.effect("R1, CMP-001 and CMP-002 compose traced repeated leaves in one flat session", () => {
  const fixture = makeFixture()
  return Effect.gen(function* () {
    const store = yield* CasStore
    const recorded = yield* session(
      withRecordLayers(
        fixture,
        Orchestration.use((service) => service.repeat("tea")),
      ),
      { mode: "record" },
    )
    expect(recorded.outcome).toEqual({
      _tag: "Completed",
      terminal: {
        _tag: "Succeeded",
        value: {
          reservations: ["reserved:tea", "reserved:tea"],
          price: 30,
        },
      },
    })
    expect(fixture.stock.calls()).toEqual(["tea", "tea"])
    expect(fixture.pricing.calls()).toEqual(["tea"])

    const historyRoot = yield* requireValue(
      fixture.tracked.latestHistory(),
      "repeat history root",
    )
    expect(recorded.history).toBe(historyRoot)
    const history = yield* observeHistory(store, historyRoot)
    expect(history.map((entry) => entry.op)).toEqual([
      "test/Composition/Stock/reserve",
      "test/Composition/Pricing/quote",
      "test/Composition/Stock/reserve",
    ])
    expect(history[0]?.request).toBe(history[2]?.request)
    expect(history[0]?.outcome).toEqual(history[2]?.outcome)

    const recordWitnessId = yield* latestWitness(fixture, "record repeat")
    expect(recorded.witness).toBe(recordWitnessId)
    const recordWitness = yield* observeWitness(store, recordWitnessId)
    expect(recordWitness.consumed).toBe(3)

    resetLiveCounts(fixture)
    const replayed = yield* session(
      withReplayLayers(
        fixture,
        Orchestration.use((service) => service.repeat("tea")),
      ),
      { mode: "replay", history: historyRoot },
    )
    expect(replayed.outcome).toEqual(recorded.outcome)
    expect(replayed.history).toBe(historyRoot)
    expect(fixture.stock.calls()).toEqual([])
    expect(fixture.pricing.calls()).toEqual([])

    const replayWitnessId = yield* latestWitness(fixture, "replay repeat")
    expect(replayed.witness).toBe(replayWitnessId)
    const replayWitness = yield* observeWitness(store, replayWitnessId)
    expect(replayWitness.consumed).toBe(history.length)
    expect(replayWitness.trace).toEqual([
      { _tag: "RecordedSubstitution", operation: "test/Composition/Stock/reserve", at: 0 },
      { _tag: "HistoryConsumed", at: 0 },
      { _tag: "RecordedSubstitution", operation: "test/Composition/Pricing/quote", at: 1 },
      { _tag: "HistoryConsumed", at: 1 },
      { _tag: "RecordedSubstitution", operation: "test/Composition/Stock/reserve", at: 2 },
      { _tag: "HistoryConsumed", at: 2 },
      { _tag: "Completed", consumed: 3 },
    ])
  }).pipe(Effect.provide(fixture.runtimeLayer))
})

it.effect("CMP-001 re-injects a nested leaf typed failure during replay", () => {
  const fixture = makeFixture()
  return Effect.gen(function* () {
    const store = yield* CasStore
    const recorded = yield* session(
      withRecordLayers(
        fixture,
        Orchestration.use((service) => service.nestedFailure("tea")),
      ),
      { mode: "record" },
    )
    expect(recorded.outcome).toEqual({
      _tag: "Completed",
      terminal: {
        _tag: "Failed",
        error: new PriceUnavailable({ sku: "unpriced" }),
      },
    })
    expect(fixture.stock.calls()).toEqual(["tea"])
    expect(fixture.pricing.calls()).toEqual(["unpriced"])

    const historyRoot = yield* requireValue(
      fixture.tracked.latestHistory(),
      "nested failure history root",
    )
    const history = yield* observeHistory(store, historyRoot)
    expect(history.map((entry) => ({ op: entry.op, outcome: entry.outcome._tag }))).toEqual([
      { op: "test/Composition/Stock/reserve", outcome: "Success" },
      { op: "test/Composition/Pricing/quote", outcome: "Failure" },
    ])

    resetLiveCounts(fixture)
    const replayed = yield* session(
      withReplayLayers(
        fixture,
        Orchestration.use((service) => service.nestedFailure("tea")),
      ),
      { mode: "replay", history: historyRoot },
    )
    expect(replayed.outcome).toEqual(recorded.outcome)
    expect(fixture.stock.calls()).toEqual([])
    expect(fixture.pricing.calls()).toEqual([])

    const replayWitnessId = yield* latestWitness(fixture, "replay nested failure")
    const replayWitness = yield* observeWitness(store, replayWitnessId)
    expect(replayWitness.consumed).toBe(history.length)
    expect(replayWitness.outcome._tag).toBe("Completed")
  }).pipe(Effect.provide(fixture.runtimeLayer))
})

it.effect("CMP-001 re-executes recovery control flow over substituted leaves", () => {
  const fixture = makeFixture()
  return Effect.gen(function* () {
    const store = yield* CasStore
    const recorded = yield* session(
      withRecordLayers(
        fixture,
        Orchestration.use((service) => service.recover("tea")),
      ),
      { mode: "record" },
    )
    expect(recorded.outcome).toEqual({
      _tag: "Completed",
      terminal: {
        _tag: "Succeeded",
        value: { reservation: "reserved:tea", price: 0 },
      },
    })

    const historyRoot = yield* requireValue(
      fixture.tracked.latestHistory(),
      "recovery history root",
    )
    const history = yield* observeHistory(store, historyRoot)
    expect(history.map((entry) => ({ op: entry.op, outcome: entry.outcome._tag }))).toEqual([
      { op: "test/Composition/Pricing/quote", outcome: "Failure" },
      { op: "test/Composition/Stock/reserve", outcome: "Success" },
    ])

    const recordWitnessId = yield* latestWitness(fixture, "record recovery")
    const recordWitness = yield* observeWitness(store, recordWitnessId)
    expect(recordWitness.trace).toEqual([
      { _tag: "LiveDelegation", operation: "test/Composition/Pricing/quote", at: 0 },
      { _tag: "OccurrenceAppended", operation: "test/Composition/Pricing/quote", at: 0 },
      { _tag: "LiveDelegation", operation: "test/Composition/Stock/reserve", at: 1 },
      { _tag: "OccurrenceAppended", operation: "test/Composition/Stock/reserve", at: 1 },
      { _tag: "Completed", consumed: 2 },
    ])

    resetLiveCounts(fixture)
    const replayed = yield* session(
      withReplayLayers(
        fixture,
        Orchestration.use((service) => service.recover("tea")),
      ),
      { mode: "replay", history: historyRoot },
    )
    expect(replayed.outcome).toEqual(recorded.outcome)
    expect(fixture.stock.calls()).toEqual([])
    expect(fixture.pricing.calls()).toEqual([])

    const replayWitnessId = yield* latestWitness(fixture, "replay recovery")
    const replayWitness = yield* observeWitness(store, replayWitnessId)
    expect(replayWitness.consumed).toBe(history.length)
    expect(replayWitness.trace).toEqual([
      { _tag: "RecordedSubstitution", operation: "test/Composition/Pricing/quote", at: 0 },
      { _tag: "HistoryConsumed", at: 0 },
      { _tag: "RecordedSubstitution", operation: "test/Composition/Stock/reserve", at: 1 },
      { _tag: "HistoryConsumed", at: 1 },
      { _tag: "Completed", consumed: 2 },
    ])
  }).pipe(Effect.provide(fixture.runtimeLayer))
})

it.effect("RPL-004 freezes a mid-orchestration mismatch without live fallback", () => {
  const fixture = makeFixture()
  return Effect.gen(function* () {
    const store = yield* CasStore
    const recorded = yield* session(
      withRecordLayers(
        fixture,
        Orchestration.use((service) => service.route("tea", "tea")),
      ),
      { mode: "record" },
    )
    expect(recorded.outcome._tag).toBe("Completed")
    const historyRoot = yield* requireValue(
      fixture.tracked.latestHistory(),
      "mismatch history root",
    )
    const history = yield* observeHistory(store, historyRoot)
    expect(history).toHaveLength(3)

    resetLiveCounts(fixture)
    const replayed = yield* session(
      withReplayLayers(
        fixture,
        Orchestration.use((service) => service.route("tea", "coffee")),
      ),
      { mode: "replay", history: historyRoot },
    )
    expect(replayed.outcome).toEqual({
      _tag: "Rejected",
      category: "RequestMismatch",
      at: 1,
    })
    expect(fixture.stock.calls()).toEqual([])
    expect(fixture.pricing.calls()).toEqual([])

    const replayWitnessId = yield* latestWitness(fixture, "replay mismatch")
    const replayWitness = yield* observeWitness(store, replayWitnessId)
    expect(replayWitness.consumed).toBe(1)
    expect(replayWitness.trace).toEqual([
      { _tag: "RecordedSubstitution", operation: "test/Composition/Stock/reserve", at: 0 },
      { _tag: "HistoryConsumed", at: 0 },
      { _tag: "TypedRejection", category: "RequestMismatch", at: 1 },
    ])
    expect(replayWitness.outcome).toEqual({
      _tag: "Rejected",
      category: "RequestMismatch",
      at: 1,
    })
  }).pipe(Effect.provide(fixture.runtimeLayer))
})
