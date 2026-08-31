import { expect, it } from "@effect/vitest"
import { Context, Effect, Layer, Schema } from "effect"
import { Cas, Replay } from "../src/index.ts"
import { ContentId } from "../src/cas/Node.ts"
import { layerMemory } from "../src/cas/Store.ts"
import type { Root } from "../src/cas/Value.ts"
import type { ServiceDescriptions } from "../src/replay/Operation.ts"
import {
  layerReplay,
  session,
} from "../src/replay/Replay.ts"
import {
  DoubleWrap,
  replayable,
  type Live,
} from "../src/replay/ServiceAdapter.ts"
import { deterministicAddress } from "./fixtures/address.ts"

class MissingEntry extends Schema.TaggedError<MissingEntry>()(
  "CasService/MissingEntry",
  { key: Schema.String },
) {}

class HydrationFailure extends Schema.TaggedError<HydrationFailure>()(
  "CasService/HydrationFailure",
  { reason: Schema.String },
) {}

interface CatalogShape {
  readonly lookup: (key: string) => Effect.Effect<string, MissingEntry>
}

class Catalog extends Context.Service<Catalog, CatalogShape>()(
  "test/effect-replay/CasService/Catalog",
) {}

const CatalogSnapshot = Schema.Struct({
  prefix: Schema.String,
  entries: Schema.Array(Schema.Struct({ key: Schema.String, value: Schema.String })),
})
type CatalogSnapshot = typeof CatalogSnapshot.Type

const CatalogDescriptions = {
  lookup: {
    id: "test/CasService/Catalog/lookup",
    revision: 1,
    request: Schema.String,
    success: Schema.String,
    failure: MissingEntry,
    leafReplay: "substitutable",
  },
} satisfies ServiceDescriptions<CatalogShape>

const projection = Cas.value({
  kindTag: 0x36,
  revision: 1,
  schema: CatalogSnapshot,
})

const snapshot: CatalogSnapshot = {
  prefix: "catalog",
  entries: [
    { key: "coffee", value: "dark" },
    { key: "tea", value: "green" },
  ],
}

const makeCatalog = (
  value: CatalogSnapshot,
  invoked?: () => void,
): CatalogShape => Catalog.of({
  lookup: (key) => Effect.suspend(() => {
    invoked?.()
    const found = value.entries.find((entry) => entry.key === key)
    return found === undefined
      ? Effect.fail(new MissingEntry({ key }))
      : Effect.succeed(`${value.prefix}:${found.value}`)
  }),
})

const runtimeLayer = () => {
  const store = layerMemory(deterministicAddress())
  return layerReplay.pipe(Layer.provideMerge(store))
}

type Equal<Left, Right> = [Left] extends [Right]
  ? [Right] extends [Left] ? true : false
  : false

it.effect("PRJ-004 fixed-root hydration matches by-value service behavior", () => {
  const hydrated = Replay.service({
    service: Catalog,
    projection,
    make: makeCatalog,
  })

  return Effect.gen(function* () {
    const root = yield* projection.put(snapshot)
    const program = Catalog.use((catalog) => catalog.lookup("tea"))
    const byValue = yield* program.pipe(
      Effect.provideService(Catalog, makeCatalog(snapshot)),
    )
    const byRoot = yield* program.pipe(Effect.provide(hydrated.layer(root)))

    expect(byRoot).toBe(byValue)

    const publicLayer = hydrated.layer(root)
    const publicOutput: Equal<Layer.Success<typeof publicLayer>, Catalog> = true
    expect(publicOutput).toBe(true)
  }).pipe(Effect.provide(runtimeLayer()))
})

it.effect("PRJ-004 keeps eager construction errors on the Layer channel", () => {
  const failing = Replay.service({
    service: Catalog,
    projection,
    make: (_value: CatalogSnapshot) =>
      Effect.fail(new HydrationFailure({ reason: "fixture rejected" })),
  })

  return Effect.gen(function* () {
    const root = yield* projection.put(snapshot)
    const error = yield* Effect.flip(
      Catalog.use((catalog) => catalog.lookup("tea")).pipe(
        Effect.provide(failing.layer(root)),
      ),
    )
    expect(error).toEqual(new HydrationFailure({ reason: "fixture rejected" }))
  }).pipe(Effect.provide(runtimeLayer()))
})

it.effect("PRJ-005 hydrates the internal live role for record then live-free replay", () => {
  let hydrations = 0
  let invocations = 0
  const hydrated = Replay.service({
    service: Catalog,
    projection,
    make: (value) => {
      hydrations += 1
      return makeCatalog(value, () => {
        invocations += 1
      })
    },
  })
  const kit = replayable(Catalog, CatalogDescriptions)

  return Effect.gen(function* () {
    const root = yield* projection.put(snapshot)
    const recordLayer = kit.record.pipe(
      Layer.provide(hydrated.layerAs(kit.live, root)),
    )
    const program = Catalog.use((catalog) => catalog.lookup("coffee"))
    const recorded = yield* session(program.pipe(Effect.provide(recordLayer)), {
      mode: "record",
    })

    expect(recorded.outcome).toEqual({
      _tag: "Completed",
      terminal: { _tag: "Succeeded", value: "catalog:dark" },
    })
    expect(hydrations).toBe(1)
    expect(invocations).toBe(1)
    if (recorded.history === undefined) {
      return yield* Effect.die("record session did not return its history root")
    }

    const replayed = yield* session(program.pipe(Effect.provide(kit.replay)), {
      mode: "replay",
      history: recorded.history,
    })
    expect(replayed.outcome).toEqual(recorded.outcome)
    expect(replayed.history).toBe(recorded.history)
    expect(hydrations).toBe(1)
    expect(invocations).toBe(1)
  }).pipe(Effect.provide(runtimeLayer()))
})

it.effect("PRJ-005 rejects a wrapped service hydrated under the live role", () => {
  const kit = replayable(Catalog, CatalogDescriptions)

  return Effect.gen(function* () {
    const root = yield* projection.put(snapshot)
    const wrapped = yield* Catalog.pipe(Effect.provide(kit.replay))
    const wrappedHydration = Replay.service({
      service: Catalog,
      projection,
      make: (_value: CatalogSnapshot) => wrapped,
    })
    const recordLayer = kit.record.pipe(
      Layer.provide(wrappedHydration.layerAs(kit.live, root)),
    )
    const error = yield* Effect.flip(Catalog.pipe(Effect.provide(recordLayer)))

    expect(error).toEqual(new DoubleWrap({ service: Catalog.key }))
  }).pipe(Effect.provide(runtimeLayer()))
})

it.effect("PRJ-005 keeps public-tag hydration distinct from the internal live role", () =>
  Effect.sync(() => {
    const compileOnlyRoot = ContentId.make("00".repeat(32)) as Root<CatalogSnapshot>
    const publicLayer = Replay.service({
      service: Catalog,
      projection,
      make: makeCatalog,
    }).layer(compileOnlyRoot)
    const publicOutput: Equal<Layer.Success<typeof publicLayer>, Catalog> = true
    expect(publicOutput).toBe(true)

    // @ts-expect-error Public-tag hydration cannot feed the internal live role.
    const liveOutput: Equal<Layer.Success<typeof publicLayer>, Live<Catalog>> = true
    void liveOutput
  }))
