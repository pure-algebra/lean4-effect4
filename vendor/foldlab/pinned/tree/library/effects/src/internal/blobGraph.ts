/** Recipe-1 blob graph materialization over an explicit ordered chunk list. */
import { Data, Effect, Schema, SchemaGetter } from "effect"
import { CasNodeInput, type CasError, type ContentId } from "../cas/Node.ts"
import type { CasStoreShape } from "../cas/Store.ts"
import { BlobManifestTag, BlobNodeTag, ChunkDataTag } from "./kindTags.ts"

export { BlobManifestTag, BlobNodeTag, ChunkDataTag }
export const ReferencedChunkRecipe = 1

/** Largest power of two strictly below n, returning one below two.
 *
 * The ratified split: a parent of `n` leaves takes the first
 * `pow2Below(n)` on the left and the rest on the right, which is what
 * makes the tree shape a function of the leaf count alone and so makes
 * a blob's address depend on nothing but its chunks. It lives here
 * because `src/cas/Blob.ts` and the finalizer below are its only
 * callers — the `internal/merkle*` mirror of the retired archive model
 * that used to hold it was reachable through this four-line rule and
 * nothing else, and is gone. */
export const pow2Below = (n: number): number =>
  n <= 2 ? 1 : 2 * pow2Below(Math.floor((n + 1) / 2))

const MaxUint32 = 0xffff_ffff
const MaxUint64 = 0xffff_ffff_ffff_ffffn

/** Exact scalar domains used by recipe-1's binary wire fields. */
export const Uint32 = Schema.Int.check(Schema.isBetween({
  minimum: 0,
  maximum: MaxUint32,
}))
export const Uint64 = Schema.BigInt.check(Schema.isBetweenBigInt({
  minimum: 0n,
  maximum: MaxUint64,
}))

/** Internal recipe violation, carried as a typed tag in the error
 * channel and translated to the public format error at the boundary —
 * never encoded, never a bare `Error`. */
export class BlobGraphError extends Data.TaggedError("BlobGraphError")<{
  readonly reason: string
}> {}

export interface BlobGraphResult {
  readonly blobRef: ContentId
  readonly treeRoot: ContentId
  readonly totalBytes: bigint
  readonly leafCount: number
}

export interface AdmittedBlobLeaf {
  readonly leafId: ContentId
  readonly totalBytes: bigint
}

const writeNat32 = (target: Uint8Array, offset: number, value: number): void => {
  target[offset] = (value >>> 24) & 0xff
  target[offset + 1] = (value >>> 16) & 0xff
  target[offset + 2] = (value >>> 8) & 0xff
  target[offset + 3] = value & 0xff
}

const writeNat64 = (target: Uint8Array, offset: number, value: bigint): void => {
  let remaining = value
  for (let index = 7; index >= 0; index -= 1) {
    target[offset + index] = Number(remaining & 0xffn)
    remaining >>= 8n
  }
}

const readNat32 = (source: Uint8Array, offset: number): number =>
  (source[offset] ?? 0) * 0x1000000
  + (source[offset + 1] ?? 0) * 0x10000
  + (source[offset + 2] ?? 0) * 0x100
  + (source[offset + 3] ?? 0)

const readNat64 = (source: Uint8Array, offset: number): bigint => {
  let value = 0n
  for (let index = 0; index < 8; index += 1) {
    value = (value << 8n) | BigInt(source[offset + index] ?? 0)
  }
  return value
}

const ManifestContent = Schema.Struct({
  recipeId: Uint32,
  totalBytes: Uint64,
  leafCount: Uint32,
})

/** The exact 16-byte, big-endian recipe manifest codec. The transformation
 * is package-owned because Effect has native bigint validation but no
 * fixed-width network-order integer codec. */
export const BlobManifestPayload = Schema.Uint8Array.check(
  Schema.isLengthBetween(16, 16),
).pipe(Schema.decodeTo(ManifestContent, {
  decode: SchemaGetter.transform((bytes) => ({
    recipeId: readNat32(bytes, 0),
    totalBytes: readNat64(bytes, 4),
    leafCount: readNat32(bytes, 12),
  })),
  encode: SchemaGetter.transform((manifest) => {
    const bytes = new Uint8Array(16)
    writeNat32(bytes, 0, manifest.recipeId)
    writeNat64(bytes, 4, manifest.totalBytes)
    writeNat32(bytes, 12, manifest.leafCount)
    return bytes
  }),
}))

export const encodeBlobManifestPayload = (manifest: {
  readonly recipeId: number
  readonly totalBytes: bigint
  readonly leafCount: number
}): Uint8Array => Schema.encodeSync(BlobManifestPayload)(manifest)

const node = (
  tag: number,
  payload: Uint8Array,
  refs: CasNodeInput["refs"],
): CasNodeInput => CasNodeInput.make({
  kind: { version: 0, tag },
  payload,
  refs,
})

const leafPayload = (index: number, chunkLength: number): Uint8Array => {
  const payload = new Uint8Array(8)
  writeNat32(payload, 0, Uint32.make(index))
  writeNat32(payload, 4, Uint32.make(chunkLength))
  return payload
}

/** Admit one ordered recipe-1 chunk and its position-binding leaf. Limits are
 * checked before either node is admitted. */
export const admitBlobLeaf = Effect.fn("BlobGraph.admitLeaf")(
  function* (
    store: CasStoreShape,
    index: number,
    totalBytes: bigint,
    bytes: Uint8Array,
  ): Effect.fn.Return<AdmittedBlobLeaf, CasError | BlobGraphError> {
    if (!Number.isInteger(index) || index < 0 || index >= MaxUint32) {
      return yield* new BlobGraphError({ reason: "recipe 1 exceeds the u32 leaf-count field" })
    }
    if (bytes.length > MaxUint32) {
      return yield* new BlobGraphError({ reason: "recipe 1 chunk exceeds the u32 length field" })
    }
    const nextTotal = totalBytes + BigInt(bytes.length)
    if (nextTotal > MaxUint64) {
      return yield* new BlobGraphError({ reason: "recipe 1 exceeds the u64 total-bytes field" })
    }
    const chunkId = yield* store.put(node(ChunkDataTag, bytes.slice(), []))
    const leafId = yield* store.put(node(
      BlobNodeTag,
      leafPayload(index, bytes.length),
      [{ id: chunkId, expectedTag: ChunkDataTag }],
    ))
    return { leafId, totalBytes: nextTotal }
  },
)

/** Finish a recipe-1 graph from already admitted leaves. This is the only
 * operation that emits the tree root and manifest. */
export const finalizeBlobGraph = Effect.fn("BlobGraph.finalize")(
  function* (
    store: CasStoreShape,
    leaves: ReadonlyArray<ContentId>,
    totalBytes: bigint,
  ): Effect.fn.Return<BlobGraphResult, CasError | BlobGraphError> {
    if (leaves.length === 0) {
      return yield* new BlobGraphError({ reason: "recipe 1 requires at least one chunk" })
    }
    if (leaves.length > MaxUint32) {
      return yield* new BlobGraphError({ reason: "recipe 1 exceeds the u32 leaf-count field" })
    }
    if (totalBytes < 0n || totalBytes > MaxUint64) {
      return yield* new BlobGraphError({ reason: "recipe 1 exceeds the u64 total-bytes field" })
    }

    const buildTree = (
      base: number,
      count: number,
    ): Effect.Effect<ContentId, CasError> => Effect.suspend(() => {
      if (count === 1) {
        const leaf = leaves[base]
        return leaf === undefined
          ? Effect.die("missing admitted blob leaf")
          : Effect.succeed(leaf)
      }
      const split = pow2Below(count)
      return Effect.flatMap(buildTree(base, split), (left) =>
        Effect.flatMap(buildTree(base + split, count - split), (right) =>
          store.put(node(BlobNodeTag, new Uint8Array(0), [
            { id: left, expectedTag: BlobNodeTag },
            { id: right, expectedTag: BlobNodeTag },
          ]))))
    })

    const treeRoot = yield* buildTree(0, leaves.length)
    const payload = encodeBlobManifestPayload({
      recipeId: ReferencedChunkRecipe,
      totalBytes,
      leafCount: leaves.length,
    })
    const blobRef = yield* store.put(node(
      BlobManifestTag,
      payload,
      [{ id: treeRoot, expectedTag: BlobNodeTag }],
    ))
    return { blobRef, treeRoot, totalBytes, leafCount: leaves.length }
  },
)

/**
 * Materialize the complete recipe-1 graph for the supplied chunk boundaries.
 * Chunk order and boundaries are semantic input here; the public blob writer's
 * fixed-size chunker is a separate stage.
 */
export const materializeBlobGraph = Effect.fn("BlobGraph.materialize")(
  function* (
    store: CasStoreShape,
    chunks: ReadonlyArray<Uint8Array>,
  ): Effect.fn.Return<BlobGraphResult, CasError | BlobGraphError> {
    if (chunks.length === 0) {
      return yield* new BlobGraphError({ reason: "recipe 1 requires at least one chunk" })
    }
    if (chunks.length > MaxUint32) {
      return yield* new BlobGraphError({ reason: "recipe 1 exceeds the u32 leaf-count field" })
    }

    const leaves: Array<ContentId> = []
    let totalBytes = 0n
    for (const bytes of chunks) {
      const admitted = yield* admitBlobLeaf(store, leaves.length, totalBytes, bytes)
      leaves.push(admitted.leafId)
      totalBytes = admitted.totalBytes
    }
    return yield* finalizeBlobGraph(store, leaves, totalBytes)
  },
)
