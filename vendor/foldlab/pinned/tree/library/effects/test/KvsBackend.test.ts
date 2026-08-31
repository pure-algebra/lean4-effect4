/**
 * The key-value backend contract: the whole store law composes over a
 * `KeyValueStore` with no filesystem anywhere, admitted bytes are
 * isolated from every caller-held buffer in both directions, and a
 * store that cannot answer degrades typed rather than silently.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Layer, Option } from "effect"
import * as KeyValueStore from "effect/unstable/persistence/KeyValueStore"
import { ByteReader, ByteWriter, objectRelativePath } from "../src/cas/Backend.ts"
import { layerKvsBackend } from "../src/cas/KvsBackend.ts"
import { CasNodeInput, ContentId } from "../src/cas/Node.ts"
import {
  CasStore,
  layerAddressSha256Live,
  layerStore,
} from "../src/cas/Store.ts"

const node = (
  payload: ReadonlyArray<number>,
  tag: number,
  refs: CasNodeInput["refs"] = [],
): CasNodeInput => CasNodeInput.make({
  kind: { version: 0, tag },
  payload: Uint8Array.from(payload),
  refs,
})

/** The store law over the byte plane over one in-memory key-value
 * store — the composition a Litestream deployment makes by swapping
 * `layerMemory` for `KeyValueStore.layerSql`. */
const overMemoryKvs = layerStore.pipe(
  Layer.provideMerge(layerKvsBackend),
  Layer.provide(Layer.mergeAll(
    KeyValueStore.layerMemory,
    layerAddressSha256Live,
  )),
)

it.effect("the store law composes over a key-value store, no filesystem", () =>
  Effect.gen(function* () {
    const store = yield* CasStore
    const reader = yield* ByteReader

    const child = node([1, 2, 3], 91)
    const childId = yield* store.put(child)
    const parentId = yield* store.put(
      node([4], 92, [{ expectedTag: 91, id: childId }]),
    )

    // The typed read law round-trips through the key-value plane.
    const loaded = yield* store.load(childId)
    expect(loaded.payload).toEqual(child.payload)
    expect(loaded.kind.tag).toBe(91)

    // Presence answers positionally, absence included.
    const absent = ContentId.make("cd".repeat(32))
    expect(yield* reader.presence([childId, absent, parentId]))
      .toEqual(["present", "missing", "present"])

    // Re-putting identical content is the identity, not a second entry.
    expect(yield* store.put(child)).toBe(childId)
  }).pipe(Effect.provide(overMemoryKvs)))

it.effect("admitted bytes are isolated from caller-held buffers", () =>
  Effect.gen(function* () {
    const writer = yield* ByteWriter
    const reader = yield* ByteReader
    const id = ContentId.make("ab".repeat(32))

    // The memory key-value store retains what it is handed by
    // reference; the backend's copy is what stops a later mutation of
    // the caller's own buffer from rewriting admitted content.
    const written = Uint8Array.from([1, 2, 3])
    yield* writer.putBytes(id, written)
    written[0] = 255

    const first = yield* reader.loadBytes(id)
    expect(Option.getOrThrow(first)).toEqual(Uint8Array.from([1, 2, 3]))

    // And a mutation of a loaded buffer does not reach back into the
    // store either.
    Option.getOrThrow(first)[0] = 255
    const second = yield* reader.loadBytes(id)
    expect(Option.getOrThrow(second)).toEqual(Uint8Array.from([1, 2, 3]))
  }).pipe(Effect.provide(
    layerKvsBackend.pipe(Layer.provide(KeyValueStore.layerMemory)),
  )))

it.effect("keys are the shared store-root layout", () =>
  Effect.gen(function* () {
    const kvs = yield* KeyValueStore.KeyValueStore
    const writer = yield* ByteWriter
    const id = ContentId.make("ab".repeat(32))

    yield* writer.putBytes(id, Uint8Array.from([7]))

    const atLayoutKey = yield* kvs.getUint8Array(objectRelativePath(id))
    expect(atLayoutKey).toEqual(Uint8Array.from([7]))
  }).pipe(Effect.provide(
    layerKvsBackend.pipe(Layer.provideMerge(KeyValueStore.layerMemory)),
  )))

it.effect("a store that cannot answer degrades typed, never silently", () => {
  const down = (method: string) =>
    Effect.fail(
      new KeyValueStore.KeyValueStoreError({ method, message: "store down" }),
    )
  const layerDown = layerKvsBackend.pipe(Layer.provide(
    Layer.succeed(
      KeyValueStore.KeyValueStore,
      KeyValueStore.make({
        clear: down("clear"),
        get: () => down("get"),
        getUint8Array: () => down("getUint8Array"),
        remove: () => down("remove"),
        set: () => down("set"),
        size: down("size"),
      }),
    ),
  ))

  return Effect.gen(function* () {
    const reader = yield* ByteReader
    const writer = yield* ByteWriter
    const id = ContentId.make("ab".repeat(32))

    // Per-key failure is reported without failing the batch.
    expect(yield* reader.presence([id, id])).toEqual(["failed", "failed"])

    const refusedRead = yield* reader.loadBytes(id).pipe(Effect.flip)
    expect(refusedRead._tag).toBe("CasBackendFailure")
    expect(refusedRead.reason).toContain("getUint8Array")

    const refusedWrite = yield* writer
      .putBytes(id, Uint8Array.from([1])).pipe(Effect.flip)
    expect(refusedWrite._tag).toBe("CasBackendFailure")
    expect(refusedWrite.reason).toContain("set")
  }).pipe(Effect.provide(layerDown))
})
