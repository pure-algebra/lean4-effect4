import { expect, it } from "@effect/vitest"
import { Effect, Encoding, Schema, SchemaGetter } from "effect"
import { Cas } from "../src/index.ts"
import {
  CasNodeInput,
  ContentId,
  ContentNotFound,
  UnknownKind,
} from "../src/cas/Node.ts"
import {
  CasStore,
  layerMemoryWith,
} from "../src/cas/Store.ts"
import {
  ProjectionCodecFailure,
  type Root,
} from "../src/cas/Value.ts"
import {
  GrammarKindTags,
  KindTagRows,
} from "../src/cas/generated/grammar/kindTags.ts"
import {
  HistoryKindTag,
  ReservedKindTags,
  WitnessKindTag,
} from "../src/internal/kindTags.ts"
import { deterministicAddress } from "./fixtures/address.ts"

const Snapshot = Schema.Struct({
  label: Schema.String,
  nested: Schema.Struct({ enabled: Schema.Boolean, count: Schema.Number }),
  items: Schema.Array(Schema.Struct({ key: Schema.String, value: Schema.Number })),
})
type Snapshot = typeof Snapshot.Type

const DomainLabel = Schema.Struct({ value: Schema.String })
interface DomainLabel extends Schema.Schema.Type<typeof DomainLabel> {}

const DomainLabelFromString = Schema.String.pipe(
  Schema.decodeTo(DomainLabel, {
    decode: SchemaGetter.transform((value) => ({ value })),
    encode: SchemaGetter.transform((label) => label.value),
  }),
)

const CustomCodecValue = Schema.Struct({
  bytes: Schema.Uint8ArrayFromHex,
  label: DomainLabelFromString,
})
interface CustomCodecValue extends Schema.Schema.Type<typeof CustomCodecValue> {}

/** The door's refusal set is the generated registry plus the two
 * replay-plane tags, which carry no registry row. */
it("PRJ-004 the refusal set is the generated registry, not a hand list", () => {
  expect([...ReservedKindTags].sort((a, b) => a - b))
    .toEqual([...GrammarKindTags, HistoryKindTag, WitnessKindTag]
      .sort((a, b) => a - b))
  // Every ratified sort AND every reserved code point, by name.
  expect(KindTagRows.every((row) => ReservedKindTags.has(row.tag))).toBe(true)
})

it("PRJ-004 refuses a caller projection at every registry tag", () => {
  for (const row of KindTagRows) {
    expect(() =>
      Cas.value({ kindTag: row.tag, revision: 1, schema: Snapshot })
    ).toThrow(/reserved/)
  }
})

/** The aliasing regression B-A named: 0x0D (`context`) and 0x0E
 * (`step`) were mintable, which handed a ratified sort's plane a second
 * public interpretation. A projection at either must refuse. */
it("PRJ-004 refuses a caller projection at 0x0D and 0x0E", () => {
  expect(() => Cas.value({ kindTag: 0x0D, revision: 1, schema: Snapshot }))
    .toThrow(/reserved/)
  expect(() => Cas.value({ kindTag: 0x0E, revision: 1, schema: Snapshot }))
    .toThrow(/reserved/)
})

it.effect("PRJ-001 rejects a root whose resident node has the wrong kind", () => {
  const first = Cas.value({ kindTag: 0x31, revision: 1, schema: Snapshot })
  const second = Cas.value({ kindTag: 0x32, revision: 1, schema: Snapshot })
  const input: Snapshot = {
    label: "inventory",
    nested: { enabled: true, count: 2 },
    items: [{ key: "tea", value: 3 }],
  }

  return Effect.gen(function* () {
    const root = yield* first.put(input)
    const error = yield* Effect.flip(second.get(root))
    expect(error).toEqual(new UnknownKind({ version: 0, tag: 0x31 }))
  }).pipe(Effect.provide(layerMemoryWith(deterministicAddress())))
})

it.effect("PRJ-002 round-trips nested values and deduplicates identical projections", () => {
  const Shapes = Schema.Union([Schema.String, Schema.Array(Schema.Number), Snapshot])
  const projection = Cas.value({ kindTag: 0x33, revision: 7, schema: Shapes })
  const input: Snapshot = {
    label: "nested",
    nested: { enabled: false, count: 17 },
    items: [
      { key: "coffee", value: 5 },
      { key: "tea", value: 9 },
    ],
  }

  return Effect.gen(function* () {
    const scalar = yield* projection.put("plain")
    const array = yield* projection.put([3, 1, 4])
    const first = yield* projection.put(input)
    const second = yield* projection.put(input)
    expect(yield* projection.get(scalar)).toBe("plain")
    expect(yield* projection.get(array)).toEqual([3, 1, 4])
    const restored = yield* projection.get(first)

    expect(second).toBe(first)
    expect(restored).toEqual(input)

    const node = yield* CasStore.use((store) => store.load(first))
    expect(new TextDecoder().decode(node.payload)).toBe(
      "{\"revision\":7,\"value\":{\"items\":[{\"key\":\"coffee\",\"value\":5},{\"key\":\"tea\",\"value\":9}],\"label\":\"nested\",\"nested\":{\"count\":17,\"enabled\":false}}}",
    )
  }).pipe(Effect.provide(layerMemoryWith(deterministicAddress())))
})

it.effect("PRJ-002 custom-codec round trip returns the same root", () => {
  const projection = Cas.value({
    kindTag: 0x39,
    revision: 1,
    schema: CustomCodecValue,
  })
  const input: CustomCodecValue = {
    bytes: new Uint8Array([0x00, 0x7f, 0xff]),
    label: { value: "fixture" } satisfies DomainLabel,
  }

  return Effect.gen(function* () {
    const first = yield* projection.put(input)
    const restored = yield* projection.get(first)
    const second = yield* projection.put(restored)

    expect(restored).toEqual(input)
    expect(second).toBe(first)
  }).pipe(Effect.provide(layerMemoryWith(deterministicAddress())))
})

it.effect("PRJ-003 reports schema decode failure as a typed projection error", () => {
  const projection = Cas.value({ kindTag: 0x34, revision: 2, schema: Snapshot })

  return Effect.gen(function* () {
    const id = yield* CasStore.use((store) => store.put(CasNodeInput.make({
      kind: { version: 0, tag: 0x34 },
      payload: new TextEncoder().encode(
        "{\"revision\":2,\"value\":{\"items\":[],\"label\":42,\"nested\":{\"count\":1,\"enabled\":true}}}",
      ),
      refs: [],
    })))
    const error = yield* Effect.flip(projection.get(id as Root<Snapshot>))

    expect(error).toBeInstanceOf(ProjectionCodecFailure)
    expect(error).toMatchObject({
      _tag: "ProjectionCodecFailure",
      direction: "decode",
      id,
    })
  }).pipe(Effect.provide(layerMemoryWith(deterministicAddress())))
})

it.effect("PRJ-003 passes a dangling projected root through as ContentNotFound", () => {
  const projection = Cas.value({ kindTag: 0x35, revision: 1, schema: Snapshot })
  const absent = ContentId.make("ff".repeat(32)) as Root<Snapshot>

  return Effect.gen(function* () {
    const error = yield* Effect.flip(projection.get(absent))
    expect(error).toEqual(new ContentNotFound({ id: absent }))
  }).pipe(Effect.provide(layerMemoryWith(deterministicAddress())))
})

it.effect("PRJ-003 reports non-finite encoded numbers without folding into StoreFailure", () => {
  const projection = Cas.value({
    kindTag: 0x37,
    revision: 1,
    // @ts-expect-error Schema.Unknown has no JSON-safe Encoded bound.
    schema: Schema.Unknown,
  })

  return Effect.gen(function* () {
    const error = yield* Effect.flip(projection.put(Number.NaN))
    expect(error).toBeInstanceOf(ProjectionCodecFailure)
    expect(error).toMatchObject({
      _tag: "ProjectionCodecFailure",
      direction: "encode",
    })
  }).pipe(Effect.provide(layerMemoryWith(deterministicAddress())))
})

it.effect("PRJ-003 rejects noncanonical payload bytes without renormalizing", () => {
  const projection = Cas.value({ kindTag: 0x38, revision: 1, schema: Schema.String })

  return Effect.gen(function* () {
    const id = yield* CasStore.use((store) => store.put(CasNodeInput.make({
      kind: { version: 0, tag: 0x38 },
      payload: new TextEncoder().encode("{\"value\":\"tea\",\"revision\":1}"),
      refs: [],
    })))
    const error = yield* Effect.flip(projection.get(id as Root<string>))
    expect(error).toMatchObject({
      _tag: "ProjectionCodecFailure",
      direction: "decode",
      id,
    })
  }).pipe(Effect.provide(layerMemoryWith(deterministicAddress())))
})
