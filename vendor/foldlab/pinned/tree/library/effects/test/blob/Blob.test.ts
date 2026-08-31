import { expect, it, layer, type Vitest } from "@effect/vitest"
import {
  Crypto,
  Encoding,
  Effect,
  Layer,
  Ref,
  Stream,
} from "effect"
import { createHash, randomBytes } from "node:crypto"
import { CasBlob } from "../../src/cas/Blob.ts"
import {
  CasNodeInput,
  ContentId,
  type CasReference,
} from "../../src/cas/Node.ts"
import {
  CasStore,
  AddressScheme,
  layerMemory,
  layerMemoryWith,
  makeCasStoreOver,
  type CasAddress,
  type CasStoreShape,
} from "../../src/cas/Store.ts"
import {
  assertCaseTable,
  assertFamilyRows,
} from "../conformance/harness.ts"
import {
  bytesEqual,
  bytesOfSize,
  invalidSliceCases,
  mrk014Binding,
  mrk018Binding,
  realManifestDecode,
  roundTripCases,
  runBlobGraphRow,
  runManifestRow,
  sliceCases,
  sliceSourceSize,
} from "./BlobFixtures.ts"
import { toyAddr } from "../fixtures/toyAddress.ts"

const TestCrypto = Layer.succeed(Crypto.Crypto, Crypto.make({
  randomBytes: (size) => new Uint8Array(randomBytes(size)),
  digest: (algorithm, bytes) => Effect.sync(() => {
    const name = algorithm.toLowerCase().replace("-", "")
    return new Uint8Array(createHash(name).update(bytes).digest())
  }),
}))

const localBacking = layerMemory.pipe(
  Layer.provideMerge(AddressScheme.layerSha256.pipe(Layer.provide(TestCrypto))),
)
const localBlobLayer = CasBlob.layer.pipe(Layer.provideMerge(localBacking))

const source = (
  bytes: Uint8Array,
  partition = [bytes.length],
): Stream.Stream<Uint8Array> => {
  const chunks: Array<Uint8Array> = []
  let offset = 0
  for (const requested of partition) {
    if (offset >= bytes.length) break
    const end = Math.min(offset + requested, bytes.length)
    chunks.push(bytes.slice(offset, end))
    offset = end
  }
  if (offset < bytes.length) chunks.push(bytes.slice(offset))
  return Stream.fromIterable(chunks)
}

const join = (chunks: ReadonlyArray<Uint8Array>): Uint8Array => {
  const length = chunks.reduce((sum, chunk) => sum + chunk.length, 0)
  const output = new Uint8Array(length)
  let offset = 0
  for (const chunk of chunks) {
    output.set(chunk, offset)
    offset += chunk.length
  }
  return output
}

const makeNode = (
  tag: number,
  payload: Uint8Array,
  refs: ReadonlyArray<CasReference>,
): CasNodeInput => CasNodeInput.make({
  kind: { version: 0, tag },
  payload,
  refs,
})

const writeNat32 = (target: Uint8Array, offset: number, value: number): void => {
  target[offset] = (value >>> 24) & 0xff
  target[offset + 1] = (value >>> 16) & 0xff
  target[offset + 2] = (value >>> 8) & 0xff
  target[offset + 3] = value & 0xff
}

const leafPayload = (index: number, length: number): Uint8Array => {
  const payload = new Uint8Array(8)
  writeNat32(payload, 0, index)
  writeNat32(payload, 4, length)
  return payload
}

const firstChunkId = (
  store: CasStoreShape,
  ref: CasBlob.BlobRef,
) => Effect.gen(function* () {
  const manifest = yield* store.load(ContentId.make(ref))
  const rootId = manifest.refs[0]?.id
  if (rootId === undefined) return yield* Effect.die("manifest has no tree root")
  const root = yield* store.load(rootId)
  const leafId = root.payload.length === 8 ? rootId : root.refs[0]?.id
  if (leafId === undefined) return yield* Effect.die("tree has no first leaf")
  const leaf = yield* store.load(leafId)
  const chunkId = leaf.refs[0]?.id
  if (chunkId === undefined) return yield* Effect.die("leaf has no chunk")
  return chunkId
})

it.effect("MRK-018 consumes every ratified blob-manifest row structurally", () =>
  assertFamilyRows(mrk018Binding, (row) =>
    runManifestRow(realManifestDecode, row)))

const toyCasAddress: CasAddress = {
  digest: (bytes) => Effect.succeed(ContentId.make(
    Encoding.encodeHex(Uint8Array.from(toyAddr(Array.from(bytes)))),
  )),
}

it.effect("MRK-014 consumes every ratified blob-graph row structurally", () =>
  CasStore.use((store) => assertFamilyRows(
    mrk014Binding,
    (row) => runBlobGraphRow(store, row).pipe(Effect.orDie),
  )).pipe(Effect.provide(layerMemoryWith(toyCasAddress))))

const registerBlobSuite = (
  test: Vitest.MethodsNonLive<CasBlob.Service | CasStore>,
): void => {
  test.effect("put and get agree on the complete recipe-1 boundary table", () =>
    assertCaseTable(roundTripCases, (size) => Effect.gen(function* () {
      const bytes = bytesOfSize(size)
      const ref = yield* CasBlob.put(source(bytes, [1, 97, 8_191, 65_536]))
      const loaded = yield* CasBlob.get(ref)
      return { length: loaded.length, matches: bytesEqual(bytes, loaded) }
    })))

  test.effect("put is deterministic across source fragmentation and inspect reports committed geometry", () =>
    Effect.gen(function* () {
      const bytes = bytesOfSize(CasBlob.ChunkSize + 37)
      const contiguous = yield* CasBlob.put(source(bytes))
      const fragmented = yield* CasBlob.put(source(bytes, [1, 2, 3, 5, 8, 13, 21]))
      expect(fragmented).toBe(contiguous)
      expect(yield* CasBlob.inspect(contiguous)).toMatchObject({
        recipeId: CasBlob.ReferencedChunkRecipe,
        totalBytes: BigInt(bytes.length),
        leafCount: 2,
      })
    }))

  test.effect("slice agrees with get at every boundary and rejects every out-of-range request", () =>
    Effect.gen(function* () {
      const bytes = bytesOfSize(sliceSourceSize)
      const ref = yield* CasBlob.put(source(bytes, [17, CasBlob.ChunkSize - 3, 11]))

      yield* assertCaseTable(sliceCases, (range) =>
        Stream.runCollect(CasBlob.slice(ref, range)).pipe(
          Effect.map(join),
          Effect.map((actual) => ({
            length: actual.length,
            matches: bytesEqual(
              actual,
              bytes.slice(Number(range.offset), Number(range.offset + range.length)),
            ),
          })),
        ))

      yield* assertCaseTable(invalidSliceCases, (range) =>
        Stream.runCollect(CasBlob.slice(ref, range)).pipe(
          Effect.match({
            onFailure: (error) => ({ _tag: "Rejected" as const, error: error._tag }),
            onSuccess: () => ({ _tag: "Accepted" as const, error: "none" }),
          }),
        ))

      // The Effect-returning sibling materializes exactly the slice bytes
      // and rejects out-of-range requests through the same validation.
      yield* assertCaseTable(sliceCases, (range) =>
        CasBlob.readRange(ref, range).pipe(
          Effect.map((actual) => ({
            length: actual.length,
            matches: bytesEqual(
              actual,
              bytes.slice(Number(range.offset), Number(range.offset + range.length)),
            ),
          })),
        ))

      yield* assertCaseTable(invalidSliceCases, (range) =>
        CasBlob.readRange(ref, range).pipe(
          Effect.match({
            onFailure: (error) => ({ _tag: "Rejected" as const, error: error._tag }),
            onSuccess: () => ({ _tag: "Accepted" as const, error: "none" }),
          }),
        ))
    }))

  test.effect("equal chunks deduplicate across positions and blobs through ordinary store references", () =>
    Effect.gen(function* () {
      const store = yield* CasStore
      const shared = bytesOfSize(CasBlob.ChunkSize)
      const leftBytes = new Uint8Array(CasBlob.ChunkSize + 1)
      leftBytes.set(shared)
      leftBytes[CasBlob.ChunkSize] = 1
      const rightBytes = leftBytes.slice()
      rightBytes[CasBlob.ChunkSize] = 2

      const left = yield* CasBlob.put(source(leftBytes))
      const right = yield* CasBlob.put(source(rightBytes))
      expect(right).not.toBe(left)
      expect(yield* firstChunkId(store, right)).toBe(yield* firstChunkId(store, left))
    }))

  test.effect("unknown recipes and tampered manifest geometry fail closed", () =>
    Effect.gen(function* () {
      const store = yield* CasStore
      const chunkId = yield* store.put(makeNode(
        CasBlob.ChunkDataTag,
        Uint8Array.of(7),
        [],
      ))
      const leafId = yield* store.put(makeNode(
        CasBlob.BlobNodeTag,
        leafPayload(0, 1),
        [{ id: chunkId, expectedTag: CasBlob.ChunkDataTag }],
      ))

      const unknownId = yield* store.put(makeNode(
        CasBlob.BlobManifestTag,
        CasBlob.encodeManifestPayload({ recipeId: 9, totalBytes: 1n, leafCount: 1 }),
        [{ id: leafId, expectedTag: CasBlob.BlobNodeTag }],
      ))
      const unknown = yield* CasBlob.get(CasBlob.BlobRef.make(unknownId)).pipe(Effect.flip)
      expect(unknown).toMatchObject({
        _tag: "CasBlobError/UnsupportedRecipe",
        recipeId: 9,
      })

      const tamperedId = yield* store.put(makeNode(
        CasBlob.BlobManifestTag,
        CasBlob.encodeManifestPayload({ recipeId: 1, totalBytes: 1n, leafCount: 2 }),
        [{ id: leafId, expectedTag: CasBlob.BlobNodeTag }],
      ))
      const tampered = yield* CasBlob.get(CasBlob.BlobRef.make(tamperedId)).pipe(Effect.flip)
      expect(tampered).toMatchObject({ _tag: "CasBlobError/Format" })
    }))

  test.effect("stream emits only a verified prefix and preserves a later terminal failure", () =>
    Effect.gen(function* () {
      const store = yield* CasStore
      const firstBytes = bytesOfSize(CasBlob.ChunkSize)
      const firstChunk = yield* store.put(makeNode(CasBlob.ChunkDataTag, firstBytes, []))
      const firstLeaf = yield* store.put(makeNode(
        CasBlob.BlobNodeTag,
        leafPayload(0, CasBlob.ChunkSize),
        [{ id: firstChunk, expectedTag: CasBlob.ChunkDataTag }],
      ))
      const badChunk = yield* store.put(makeNode(
        CasBlob.ChunkDataTag,
        Uint8Array.of(1, 2),
        [],
      ))
      const secondLeaf = yield* store.put(makeNode(
        CasBlob.BlobNodeTag,
        leafPayload(1, 1),
        [{ id: badChunk, expectedTag: CasBlob.ChunkDataTag }],
      ))
      const root = yield* store.put(makeNode(
        CasBlob.BlobNodeTag,
        new Uint8Array(0),
        [
          { id: firstLeaf, expectedTag: CasBlob.BlobNodeTag },
          { id: secondLeaf, expectedTag: CasBlob.BlobNodeTag },
        ],
      ))
      const manifest = yield* store.put(makeNode(
        CasBlob.BlobManifestTag,
        CasBlob.encodeManifestPayload({
          recipeId: 1,
          totalBytes: BigInt(CasBlob.ChunkSize + 1),
          leafCount: 2,
        }),
        [{ id: root, expectedTag: CasBlob.BlobNodeTag }],
      ))

      const observed: Array<number> = []
      const result = yield* CasBlob.stream(CasBlob.BlobRef.make(manifest)).pipe(
        Stream.runForEach((chunk) => Effect.sync(() => observed.push(chunk.length))),
        Effect.result,
      )
      expect(observed).toEqual([CasBlob.ChunkSize])
      expect(result._tag).toBe("Failure")
      if (result._tag === "Failure") {
        expect(result.failure).toMatchObject({ _tag: "CasBlobError/Format" })
      }
    }))

}

layer(localBlobLayer)("CasBlob local memory lane", (test) => {
  registerBlobSuite(test)
})
