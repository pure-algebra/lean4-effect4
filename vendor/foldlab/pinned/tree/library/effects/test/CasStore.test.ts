import { expect, it } from "@effect/vitest"
import { Effect, Encoding, Option, Schema } from "effect"
import {
  Byte,
  CasNodeInput,
  ContentId,
  StoreFailure,
  type CasError,
} from "../src/cas/Node.ts"
import {
  makeMemoryBackend,
} from "../src/cas/Backend.ts"
import {
  CasStore,
  decodeCasNode,
  encodeCasNode,
  layerMemoryWith,
  makeCasStoreOver,
  type CasAddress,
} from "../src/cas/Store.ts"
import { assertFamilyRows, ManifestModel } from "./conformance/harness.ts"
import { deterministicAddress } from "./fixtures/address.ts"

const Bytes = Schema.Array(Byte)
const AddressBytes = Bytes.check(Schema.isLengthBetween(32, 32))

const ManifestNode = Schema.Struct({
  payload: Bytes,
  refs: Schema.Array(Schema.Struct({
    addr: AddressBytes,
    expectedTag: Byte,
  })),
  tag: Byte,
  version: Byte,
})
type ManifestNode = typeof ManifestNode.Type

const CAS001Row = Schema.Union([
    Schema.Struct({
      case: Schema.String,
      expect: Schema.Struct({ decoded: Schema.Null }),
      input: Schema.Struct({ bytes: Bytes }),
    }),
    Schema.Struct({
      case: Schema.String,
      expect: Schema.Struct({ bytes: Bytes, roundtrip: Schema.Boolean }),
      input: Schema.Struct({ node: ManifestNode }),
    }),
  ])

const CAS002Row = Schema.Struct({
    case: Schema.String,
    expect: Schema.Union([
      Schema.Struct({ admitted: Schema.Literal(true) }),
      Schema.Struct({
        admitted: Schema.Literal(false),
        clause: Schema.Literal("CasError/DanglingReference"),
        missing: AddressBytes,
      }),
      Schema.Struct({
        actualTag: Byte,
        admitted: Schema.Literal(false),
        clause: Schema.Literal("CasError/WrongKindReference"),
        expectedTag: Byte,
        ref: AddressBytes,
      }),
    ]),
    input: Schema.Struct({
      node: ManifestNode,
      store: Schema.Array(Schema.Struct({
        addr: AddressBytes,
        node: ManifestNode,
      })),
    }),
  })

const CAS001Binding = {
  family: "CAS-001",
  model: ManifestModel,
  row: CAS001Row,
  hasOracle: false,
} as const

const CAS002Binding = {
  family: "CAS-002",
  model: ManifestModel,
  row: CAS002Row,
  hasOracle: false,
} as const

const contentIdFromBytes = (bytes: ReadonlyArray<number>): ContentId =>
  ContentId.make(Encoding.encodeHex(Uint8Array.from(bytes)))

const contentIdToBytes = (id: ContentId): ReadonlyArray<number> => {
  const decoded = Encoding.decodeHex(id)
  if (decoded._tag === "Failure") {
    throw new Error("validated ContentId failed hex decoding")
  }
  return Array.from(decoded.success)
}

const decodeManifestNode = (node: ManifestNode) =>
  CasNodeInput.makeEffect({
    kind: { version: node.version, tag: node.tag },
    payload: Uint8Array.from(node.payload),
    refs: node.refs.map((ref) => ({
      id: contentIdFromBytes(ref.addr),
      expectedTag: ref.expectedTag,
    })),
  }).pipe(Effect.orDie)

const manifestNodeFromCas = (node: CasNodeInput): ManifestNode => ({
  payload: Array.from(node.payload),
  refs: node.refs.map((ref) => ({
    addr: contentIdToBytes(ref.id),
    expectedTag: ref.expectedTag,
  })),
  tag: node.kind.tag,
  version: node.kind.version,
})

const nodesEqual = (left: CasNodeInput, right: CasNodeInput): boolean => {
  if (left.kind.version !== right.kind.version || left.kind.tag !== right.kind.tag) {
    return false
  }
  if (left.payload.length !== right.payload.length || left.refs.length !== right.refs.length) {
    return false
  }
  for (let index = 0; index < left.payload.length; index += 1) {
    if (left.payload[index] !== right.payload[index]) return false
  }
  for (let index = 0; index < left.refs.length; index += 1) {
    const l = left.refs[index]
    const r = right.refs[index]
    if (l === undefined || r === undefined) return false
    if (l.id !== r.id || l.expectedTag !== r.expectedTag) return false
  }
  return true
}

const normalizeAdmissionError = (error: CasError): unknown => {
  switch (error._tag) {
    case "CasError/DanglingReference":
      return {
        admitted: false,
        clause: error._tag,
        missing: contentIdToBytes(error.missing),
      }
    case "CasError/WrongKindReference":
      return {
        actualTag: error.actualTag,
        admitted: false,
        clause: error._tag,
        expectedTag: error.expectedTag,
        ref: contentIdToBytes(error.ref),
      }
    default:
      return { admitted: false, clause: error._tag }
  }
}

const mappedAddress = (
  entries: ReadonlyMap<string, ContentId>,
): CasAddress => ({
  digest: (canonicalBytes) => {
    const id = entries.get(Encoding.encodeHex(canonicalBytes))
    return id === undefined
      ? Effect.fail(new StoreFailure({ reason: "No fixture address for canonical bytes" }))
      : Effect.succeed(id)
  },
})

it.effect("CAS-001 consumes every ratified CODEC row structurally", () =>
  assertFamilyRows(CAS001Binding, (row) =>
    Effect.gen(function* () {
      if ("node" in row.input) {
        const node = yield* decodeManifestNode(row.input.node)
        const encoded = encodeCasNode(node)
        const decoded = Option.getOrUndefined(decodeCasNode(encoded))
        const actual = {
          bytes: Array.from(encoded),
          roundtrip: decoded !== undefined && nodesEqual(decoded, node),
        }
        return actual
      } else {
        const decoded = Option.getOrUndefined(
          decodeCasNode(Uint8Array.from(row.input.bytes)),
        )
        const actual = {
          decoded: decoded === undefined ? null : manifestNodeFromCas(decoded),
        }
        return actual
      }
    })))

it.effect("CAS-002 consumes every ratified REJECTION-CLAUSE row structurally", () =>
  assertFamilyRows(CAS002Binding, (row) =>
    Effect.gen(function* () {
      const candidate = yield* decodeManifestNode(row.input.node)
      const residents: Array<{
        readonly id: ContentId
        readonly node: CasNodeInput
      }> = []
      for (const binding of row.input.store) {
        residents.push({
          id: contentIdFromBytes(binding.addr),
          node: yield* decodeManifestNode(binding.node),
        })
      }

      const addresses = new Map<string, ContentId>()
      for (const resident of residents) {
        addresses.set(Encoding.encodeHex(encodeCasNode(resident.node)), resident.id)
      }
      addresses.set(
        Encoding.encodeHex(encodeCasNode(candidate)),
        contentIdFromBytes(Array(32).fill(0xfe)),
      )

      const actual = yield* Effect.gen(function* () {
        const store = yield* CasStore
        for (const resident of residents) {
          const id = yield* store.put(resident.node).pipe(Effect.orDie)
          expect(id).toBe(resident.id)
        }
        return yield* store.put(candidate).pipe(Effect.match({
          onFailure: normalizeAdmissionError,
          onSuccess: () => ({ admitted: true as const }),
        }))
      }).pipe(Effect.provide(layerMemoryWith(mappedAddress(addresses))))

      return actual
    })))

it.effect("the in-memory adapter re-verifies load and names caller-requested misses", () => {
  const firstId = contentIdFromBytes(Array(32).fill(0x11))
  const secondId = contentIdFromBytes(Array(32).fill(0x22))
  let digestCalls = 0
  const changingAddress: CasAddress = {
    digest: () => Effect.sync(() => digestCalls++ === 0 ? firstId : secondId),
  }

  return Effect.gen(function* () {
    const node = CasNodeInput.make({
      kind: { version: 0, tag: 3 },
      payload: Uint8Array.from([1, 2, 3]),
      refs: [],
    })

    const store = yield* CasStore
    const id = yield* store.put(node)
    expect(id).toBe(firstId)

    const mismatch = yield* store.load(id).pipe(Effect.match({
      onFailure: (error) => error,
      onSuccess: () => undefined,
    }))
    expect(mismatch?._tag).toBe("CasError/AddressMismatch")

    const missing = yield* store.load(contentIdFromBytes(Array(32).fill(0x33))).pipe(
      Effect.match({
        onFailure: (error) => error,
        onSuccess: () => undefined,
      }),
    )
    expect(missing?._tag).toBe("CasError/ContentNotFound")
  }).pipe(Effect.provide(layerMemoryWith(changingAddress)))
})

it.effect("the M2 in-memory adapter loads an immutable admitted node", () => {
  const id = contentIdFromBytes(Array(32).fill(0x44))
  const stableAddress: CasAddress = { digest: () => Effect.succeed(id) }

  return Effect.gen(function* () {
    const store = yield* CasStore
    const input = CasNodeInput.make({
      kind: { version: 0, tag: 4 },
      payload: Uint8Array.from([7, 8, 9]),
      refs: [],
    })

    yield* store.put(input)
    input.payload[0] = 0xff

    const first = yield* store.load(id)
    expect(Array.from(first.payload)).toEqual([7, 8, 9])
    first.payload[1] = 0xff

    const second = yield* store.load(id)
    expect(Array.from(second.payload)).toEqual([7, 8, 9])
  }).pipe(Effect.provide(layerMemoryWith(stableAddress)))
})

it.effect("admission verifies every resident reference before trusting its tag", () =>
  Effect.gen(function* () {
    const parent = (id: ContentId, expectedTag: number) => CasNodeInput.make({
      kind: { version: 0, tag: 90 },
      payload: new Uint8Array(0),
      refs: [{ id, expectedTag }],
    })
    const child = (payload: ReadonlyArray<number>, tag: number) => CasNodeInput.make({
      kind: { version: 0, tag },
      payload: Uint8Array.from(payload),
      refs: [],
    })

    const run = (prepare: (
      address: CasAddress,
      putRaw: (id: ContentId, bytes: Uint8Array) => Effect.Effect<void, StoreFailure>,
    ) => Effect.Effect<
      { readonly id: ContentId; readonly expectedTag: number },
      StoreFailure
    >) =>
      Effect.gen(function* () {
        const address = deterministicAddress()
        const backend = makeMemoryBackend()
        const prepared = yield* prepare(
          address,
          (id, bytes) => backend.writer.putBytes(id, bytes).pipe(
            Effect.mapError((error) => new StoreFailure({ reason: error.reason })),
          ),
        )
        const store = makeCasStoreOver(address, backend.reader, backend.writer)
        return yield* store.put(parent(prepared.id, prepared.expectedTag)).pipe(Effect.flip)
      })

    const missing = yield* run((_address, _putRaw) => Effect.succeed({
      id: ContentId.make("a1".repeat(32)),
      expectedTag: 7,
    }))
    expect(missing._tag).toBe("CasError/DanglingReference")

    const nonCanonical = yield* run((_address, putRaw) => Effect.gen(function* () {
      const id = ContentId.make("a2".repeat(32))
      yield* putRaw(id, Uint8Array.of(0xff))
      return { id, expectedTag: 7 }
    }))
    expect(nonCanonical._tag).toBe("CasError/NonCanonicalBytes")

    const addressMismatch = yield* run((address, putRaw) => Effect.gen(function* () {
      const bytes = encodeCasNode(child([1], 7))
      const actual = yield* address.digest(bytes)
      const id = actual === ContentId.make("a3".repeat(32))
        ? ContentId.make("a4".repeat(32))
        : ContentId.make("a3".repeat(32))
      yield* putRaw(id, bytes)
      return { id, expectedTag: 7 }
    }))
    expect(addressMismatch._tag).toBe("CasError/AddressMismatch")

    const unknownKind = yield* run((address, putRaw) => Effect.gen(function* () {
      const bytes = encodeCasNode(CasNodeInput.make({
        kind: { version: 1, tag: 7 },
        payload: new Uint8Array(0),
        refs: [],
      }))
      const id = yield* address.digest(bytes)
      yield* putRaw(id, bytes)
      return { id, expectedTag: 7 }
    }))
    expect(unknownKind._tag).toBe("CasError/UnknownKind")

    const wrongKind = yield* run((address, putRaw) => Effect.gen(function* () {
      const bytes = encodeCasNode(child([2], 7))
      const id = yield* address.digest(bytes)
      yield* putRaw(id, bytes)
      return { id, expectedTag: 8 }
    }))
    expect(wrongKind).toMatchObject({
      _tag: "CasError/WrongKindReference",
      actualTag: 7,
      expectedTag: 8,
    })
  }))
