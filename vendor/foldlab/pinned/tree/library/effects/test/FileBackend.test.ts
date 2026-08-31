/**
 * The file backend contract, proved against the pure in-memory
 * `FileSystem` test layer — no platform reach anywhere: fan-out layout,
 * temp+rename publish, idempotent re-put, dumb reads re-verified by the
 * store law above, and the empty-file roots registry.
 */
import { expect, it } from "@effect/vitest"
import { Effect, FileSystem, Layer, Option, Path, PlatformError } from "effect"
import { BunPath } from "@effect/platform-bun"
import {
  ByteReader,
  makeMemoryBackend,
  RootStore,
} from "../src/cas/Backend.ts"
import {
  makeFileBackend,
  makeFileBackendFromFileUrl,
  normalizeStoreRootWith,
  storeRootFromFileUrl,
} from "../src/cas/FileBackend.ts"
import { CasNodeInput, ContentId } from "../src/cas/Node.ts"
import {
  CasStore,
  layerAddressSha256Live,
  layerFile,
} from "../src/cas/Store.ts"
import { makeMemoryFs, type MemoryFs } from "./MemoryFsHarness.ts"

const storeRoot = "store"

const layerHarness = (memory: MemoryFs) => layerFile(storeRoot).pipe(
  Layer.provide(Layer.mergeAll(
    Layer.succeed(FileSystem.FileSystem, memory.fs),
    layerAddressSha256Live,
  )),
)

const node = (
  payload: ReadonlyArray<number>,
  tag: number,
  refs: CasNodeInput["refs"] = [],
): CasNodeInput => CasNodeInput.make({
  kind: { version: 0, tag },
  payload: Uint8Array.from(payload),
  refs,
})

const fixedId = (byte: string): ContentId => ContentId.make(byte.repeat(32))

it.effect("memory byte joins copy input, deduplicate equality, and reject collisions", () =>
  Effect.gen(function* () {
    const backend = makeMemoryBackend()
    const id = fixedId("11")
    const original = Uint8Array.of(1, 2, 3)
    yield* backend.writer.putBytes(id, original)
    original[0] = 9
    yield* backend.writer.putBytes(id, Uint8Array.of(1, 2, 3))

    const collision = yield* backend.writer.putBytes(id, Uint8Array.of(1, 2, 4)).pipe(
      Effect.flip,
    )
    expect(collision._tag).toBe("CasBackendFailure")
    expect(Option.getOrThrow(yield* backend.reader.loadBytes(id)))
      .toEqual(Uint8Array.of(1, 2, 3))
  }))

it.effect("file byte joins choose one atomic winner and never overwrite it", () =>
  Effect.gen(function* () {
    const memory = yield* makeMemoryFs
    const backend = makeFileBackend(memory.fs, storeRoot)
    const equalId = fixedId("22")
    const equal = Uint8Array.of(4, 5, 6)
    const equalResults = yield* Effect.all([
      backend.writer.putBytes(equalId, equal).pipe(Effect.result),
      backend.writer.putBytes(equalId, equal.slice()).pipe(Effect.result),
    ], { concurrency: "unbounded" })
    expect(equalResults.every((result) => result._tag === "Success")).toBe(true)

    const collisionId = fixedId("33")
    const left = Uint8Array.of(7, 8)
    const right = Uint8Array.of(9, 10)
    const results = yield* Effect.all([
      backend.writer.putBytes(collisionId, left).pipe(Effect.result),
      backend.writer.putBytes(collisionId, right).pipe(Effect.result),
    ], { concurrency: "unbounded" })
    expect(results.filter((result) => result._tag === "Success")).toHaveLength(1)
    expect(results.filter((result) => result._tag === "Failure")).toHaveLength(1)

    const winner = Option.getOrThrow(yield* backend.reader.loadBytes(collisionId))
    const loser = winner[0] === left[0] ? right : left
    const refused = yield* backend.writer.putBytes(collisionId, loser).pipe(Effect.flip)
    expect(refused._tag).toBe("CasBackendFailure")
    expect(Option.getOrThrow(yield* backend.reader.loadBytes(collisionId))).toEqual(winner)
    expect([...((yield* memory.dump).keys())].filter((path) => path.includes("put-")))
      .toEqual([])
  }))

it.effect("file publication reports temp cleanup failure instead of claiming success", () =>
  Effect.gen(function* () {
    const memory = yield* makeMemoryFs
    const cleanupFailure = PlatformError.systemError({
      _tag: "PermissionDenied",
      method: "remove",
      module: "FileSystem",
      pathOrDescriptor: "temp",
    })
    const fs: FileSystem.FileSystem = {
      ...memory.fs,
      remove: () => Effect.fail(cleanupFailure),
    }
    const backend = makeFileBackend(fs, storeRoot)
    const error = yield* backend.writer.putBytes(fixedId("44"), Uint8Array.of(1)).pipe(
      Effect.flip,
    )
    expect(error._tag).toBe("CasBackendFailure")
    expect([...((yield* memory.dump).keys())].some((path) => path.includes("put-")))
      .toBe(true)
  }))

it.effect("file roots normalize Windows input separators to portable emitted paths", () =>
  Effect.gen(function* () {
    const memory = yield* makeMemoryFs
    const backend = makeFileBackend(memory.fs, "portable\\nested\\")
    const id = fixedId("55")
    yield* backend.writer.putBytes(id, Uint8Array.of(1, 2))
    yield* backend.roots.publish(id)

    const paths = [...((yield* memory.dump).keys())]
    expect(paths).toContain(`portable/nested/objects/${id.slice(0, 2)}/${id.slice(2)}`)
    expect(paths).toContain(`portable/nested/roots/${id}`)
    expect(paths.every((path) => !path.includes("\\"))).toBe(true)
  }))

it.effect("Effect Path normalizes native roots and resolves file URLs per host", () =>
  Effect.gen(function* () {
    const windows = yield* storeRootFromFileUrl(
      new URL("file:///C:/estate/cas"),
    ).pipe(Effect.provide(BunPath.layerWin32))
    const posix = yield* storeRootFromFileUrl(
      new URL("file:///var/lib/cas"),
    ).pipe(Effect.provide(BunPath.layerPosix))

    expect(windows).toBe("C:\\estate\\cas")
    expect(posix).toBe("/var/lib/cas")

    const normalizedWindows = yield* Effect.gen(function* () {
      const path = yield* Path.Path
      return normalizeStoreRootWith(path, "C:\\estate\\tmp\\..\\cas\\")
    }).pipe(Effect.provide(BunPath.layerWin32))
    expect(normalizedWindows).toBe("C:\\estate\\cas")
  }))

it.effect("file-URL backend publication stays in the normalized POSIX root", () =>
  Effect.gen(function* () {
    const memory = yield* makeMemoryFs
    const backend = yield* makeFileBackendFromFileUrl(
      memory.fs,
      new URL("file:///portable/nested/../store"),
    ).pipe(Effect.provide(BunPath.layerPosix))
    const id = fixedId("56")
    yield* backend.writer.putBytes(id, Uint8Array.of(1, 2, 3))
    yield* backend.roots.publish(id)

    const paths = [...((yield* memory.dump).keys())]
    expect(paths).toContain(`/portable/store/objects/${id.slice(0, 2)}/${id.slice(2)}`)
    expect(paths).toContain(`/portable/store/roots/${id}`)
    expect(paths.every((path) => !path.includes(".."))).toBe(true)
  }))

it.effect("round-trips through the store law and lands the fan-out layout", () =>
  Effect.gen(function* () {
    const memory = yield* makeMemoryFs
    yield* Effect.gen(function* () {
      const store = yield* CasStore
      const child = node([1, 2, 3], 91)
      const id = yield* store.put(child)
      expect(yield* store.put(child)).toBe(id)
      expect(yield* store.load(id)).toEqual(child)

      // The address is the path: objects/<2 hex>/<62 hex>, and the
      // publish left no temp file — and no temp SCAFFOLD DIRECTORY —
      // behind: the platform realizes a temp file as a directory with
      // the file inside, so an unscoped temp leaks a directory per
      // fresh write.
      const held = yield* memory.dump
      expect(held.has(`${storeRoot}/objects/${id.slice(0, 2)}/${id.slice(2)}`))
        .toBe(true)
      expect([...held.keys()].filter((key) => key.includes("put-"))).toEqual([])
      const heldDirectories = yield* memory.dumpDirectories
      expect([...heldDirectories].filter((key) => key.includes("put-"))).toEqual([])

      // The law, not the backend, refuses a dangling closure.
      const dangling = node([9], 92, [{
        expectedTag: 91,
        id: ContentId.make("ab".repeat(32)),
      }])
      const refused = yield* store.put(dangling).pipe(Effect.flip)
      expect(refused._tag).toBe("CasError/DanglingReference")
    }).pipe(Effect.provide(layerHarness(memory)))
  }))

it.effect("reads stay dumb and the law refuses corrupted bytes typed", () =>
  Effect.gen(function* () {
    const memory = yield* makeMemoryFs
    yield* Effect.gen(function* () {
      const store = yield* CasStore
      const id = yield* store.put(node([7, 7, 7], 91))
      const path = `${storeRoot}/objects/${id.slice(0, 2)}/${id.slice(2)}`

      // Flip one payload byte directly in storage: still a canonical
      // encoding, no longer the digest's pre-image.
      const held = yield* memory.dump
      const corrupted = held.get(path)!.slice()
      corrupted[6] = corrupted[6] === 0 ? 1 : 0
      yield* memory.poke(path, corrupted)

      const refused = yield* store.load(id).pipe(Effect.flip)
      expect(refused._tag).toBe("CasError/AddressMismatch")
    }).pipe(Effect.provide(layerHarness(memory)))
  }))

it.effect("presence answers positionally and roots persist as empty files", () =>
  Effect.gen(function* () {
    const memory = yield* makeMemoryFs
    yield* Effect.gen(function* () {
      const store = yield* CasStore
      const reader = yield* ByteReader
      const roots = yield* RootStore

      // An unpublished store lists no roots — absent directory included.
      expect(yield* roots.list).toEqual([])

      const id = yield* store.put(node([4, 5], 91))
      const absent = ContentId.make("cd".repeat(32))
      expect(yield* reader.presence([id, absent])).toEqual(["present", "missing"])

      yield* roots.publish(id)
      yield* roots.publish(id)
      expect(yield* roots.list).toEqual([id])
      expect((yield* memory.dump).get(`${storeRoot}/roots/${id}`))
        .toEqual(new Uint8Array(0))
    }).pipe(Effect.provide(layerHarness(memory)))
  }))
