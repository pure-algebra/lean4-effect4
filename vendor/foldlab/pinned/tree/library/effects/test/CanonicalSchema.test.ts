/** Native Effect Schema representation as canonical CAS content. */
import { expect, it } from "@effect/vitest"
import {
  cast,
  Effect,
  Encoding,
  Option,
  Schema,
  SchemaRepresentation,
} from "effect"
import { Cas } from "../src/index.ts"
import { ContentId, UnknownKind } from "../src/cas/Node.ts"
import { CasStore, layerMemoryWith } from "../src/cas/Store.ts"
import { deterministicAddress } from "./fixtures/address.ts"

const CS = Cas.CanonicalSchema
const address = deterministicAddress()

const snapshotSchema = Schema.Struct({
  label: Schema.String,
  count: Schema.Int,
  note: Schema.optionalKey(Schema.Array(Schema.String)),
  author: CS.ref(0x21),
})

it("canonical bytes normalize order-insensitive object declarations", () => {
  const reordered = Schema.Struct({
    author: CS.ref(0x21),
    note: Schema.optionalKey(Schema.Array(Schema.String)),
    count: Schema.Int,
    label: Schema.String,
  })
  expect(Encoding.encodeHex(CS.bytesOf(snapshotSchema)))
    .toBe(Encoding.encodeHex(CS.bytesOf(reordered)))
  expect(Encoding.encodeHex(CS.bytesOf(Schema.String)))
    .not.toBe(Encoding.encodeHex(CS.bytesOf(Schema.Int)))
})

it("a carrier snapshots a native representation and malformed annotations fail closed", () => {
  const runtime = Schema.Struct({ label: Schema.String, count: Schema.Int })
  const carrying = runtime.pipe(CS.annotate(snapshotSchema))

  expect(Option.getOrThrow(CS.astOf(carrying))._tag).toBe("Objects")
  expect(Encoding.encodeHex(Option.getOrThrow(CS.bytesFor(carrying))))
    .toBe(Encoding.encodeHex(CS.bytesOf(snapshotSchema)))

  const corrupted = runtime.annotate({ [CS.AnnotationKey]: 42 })
  expect(Option.isNone(CS.astOf(corrupted))).toBe(true)
  expect(Option.isNone(CS.bytesFor(corrupted))).toBe(true)
})

it("a pin survives on either side of a check", () => {
  // `annotate` lands on the LAST CHECK when a carrier has checks, and
  // Effect resolves annotations from that same slot. A pin attached
  // after `.check(...)` used to be written into a slot the reader never
  // looked at, so the carrier silently fell back to its own native
  // representation.
  const expected = Encoding.encodeHex(CS.bytesOf(snapshotSchema))
  const after = Schema.String.check(Schema.isMinLength(2))
    .pipe(CS.annotate(snapshotSchema))
  const before = Schema.String.pipe(CS.annotate(snapshotSchema))
    .check(Schema.isMinLength(2))

  for (const carrier of [after, before]) {
    expect(Option.getOrThrow(CS.astOf(carrier))._tag).toBe("Objects")
    expect(Encoding.encodeHex(Option.getOrThrow(CS.bytesFor(carrier))))
      .toBe(expected)
  }

  // Fail-closed is unchanged in the check slot too.
  const corrupted = Schema.String.check(Schema.isMinLength(2))
    .annotate({ [CS.AnnotationKey]: 42 })
  expect(Option.isNone(CS.bytesFor(corrupted))).toBe(true)
})

it.effect("schemas are content: put, address identity, exact frozen get", () =>
  Effect.gen(function* () {
    const id = yield* CS.put(snapshotSchema)
    expect(id).toBe(yield* CS.addressWith(address)(snapshotSchema))

    const back = yield* CS.get(id)
    expect(SchemaRepresentation.toJson(back)).toEqual(
      SchemaRepresentation.toJson(CS.representationOf(snapshotSchema)),
    )
    expect(Object.isFrozen(back)).toBe(true)
    expect(Object.isFrozen(back.representation)).toBe(true)
    expect(yield* CS.put(snapshotSchema)).toBe(id)
  }).pipe(Effect.provide(layerMemoryWith(address))))

it.effect("get refuses a resident node of another kind", () =>
  Effect.gen(function* () {
    const store = yield* CasStore
    const alien = yield* store.put({
      kind: { version: 0, tag: 0x22 },
      payload: new Uint8Array([1, 2, 3]),
      refs: [],
    })
    expect(yield* Effect.flip(CS.get(alien)))
      .toEqual(new UnknownKind({ version: 0, tag: 0x22 }))
  }).pipe(Effect.provide(layerMemoryWith(address))))

it("the schema kind tag remains reserved against user projections", () => {
  expect(() => Cas.value({
    kindTag: CS.KindTag,
    revision: 0,
    schema: Schema.Struct({ x: Schema.String }),
  })).toThrow(/reserved/)
})

it("strict native documents reject root and nested excess properties", () => {
  const json = SchemaRepresentation.toJson(CS.representationOf(snapshotSchema))
  const rootExcess = {
    ...(structuredClone(json) as Schema.JsonObject),
    extra: true,
  }
  expect(() => CS.fromJson(rootExcess)).toThrow()

  const nestedExcess = structuredClone(json) as unknown as {
    representation: {
      propertySignatures: Array<{ type: Record<string, Schema.Json> }>
    }
    references: Record<string, Schema.Json>
  }
  nestedExcess.representation.propertySignatures[0]!.type.extra = true
  expect(() => CS.fromJson(cast(nestedExcess))).toThrow()
})

it("fromAst and annotate retain immutable snapshots, not caller-owned data", () => {
  const source = SchemaRepresentation.fromJson(
    SchemaRepresentation.toJson(CS.representationOf(snapshotSchema)),
  )
  const derived = CS.fromRepresentation(source)
  const annotated = CS.annotate(source)(Schema.String)
  const before = Encoding.encodeHex(Option.getOrThrow(CS.bytesFor(derived)))

  const mutable = source as unknown as {
    representation: {
      propertySignatures: Array<{ type: { _tag: string } }>
    }
  }
  mutable.representation.propertySignatures[0]!.type._tag = "Number"

  for (const carrier of [derived, annotated]) {
    const ast = Option.getOrThrow(CS.astOf(carrier))
    expect(ast._tag).toBe("Objects")
    expect(Object.isFrozen(ast)).toBe(true)
    expect(Encoding.encodeHex(Option.getOrThrow(CS.bytesFor(carrier))))
      .toBe(before)
  }
})

it.effect("revision 1 and legacy revision 0 reject excess data", () =>
  Effect.gen(function* () {
    const store = yield* CasStore
    const malformedV1 = yield* store.put({
      kind: { version: 0, tag: CS.KindTag },
      payload: new TextEncoder().encode(
        '{"revision":1,"value":{"extra":true,"references":{},"representation":{"_tag":"String","checks":[]}}}',
      ),
      refs: [],
    })
    expect((yield* CS.get(malformedV1).pipe(Effect.flip))._tag)
      .toBe("ProjectionCodecFailure")

    const malformedV0 = yield* store.put({
      kind: { version: 0, tag: CS.KindTag },
      payload: new TextEncoder().encode(
        '{"revision":0,"value":{"_tag":"String","extra":true}}',
      ),
      refs: [],
    })
    expect((yield* CS.get(malformedV0).pipe(Effect.flip))._tag)
      .toBe("ProjectionCodecFailure")
  }).pipe(Effect.provide(layerMemoryWith(address))))

it.effect("a revived native reference retains value-plane edge semantics", () =>
  Effect.gen(function* () {
    const Author = Cas.value({
      kindTag: 0x21,
      revision: 0,
      schema: Schema.Struct({ name: Schema.String }),
    })
    const identity = Schema.Struct({
      title: Schema.String,
      author: CS.ref(0x21),
    })
    const revived = CS.fromRepresentation(CS.representationOf(identity)) as
      Schema.Codec<{
        readonly title: string
        readonly author: Cas.Root<unknown>
      }, Schema.Json>
    const Doc = Cas.value({ kindTag: 0x22, revision: 0, schema: revived })

    const author = yield* Author.put({ name: "pierce" })
    const doc = yield* Doc.put({ title: "types", author: cast(author) })
    const back = yield* Doc.get(doc)
    expect(back).toEqual({ title: "types", author })

    const ghost: Cas.Root<unknown> = cast(ContentId.make("ab".repeat(32)))
    const refusal = yield* Doc.put({ title: "nope", author: ghost }).pipe(Effect.flip)
    expect(refusal._tag).toBe("CasError/DanglingReference")
  }).pipe(Effect.provide(layerMemoryWith(address))))
