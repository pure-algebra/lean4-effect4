/**
 * The path-reader contract: it reads exactly the store-root layout the
 * file backend writes — publish-by-directory proved end to end — and a
 * host that cannot answer degrades typed, never silently.
 */
import { expect, it } from "@effect/vitest"
import { Effect, FileSystem, Layer, Option } from "effect"
import { ByteReader, objectRelativePath } from "../src/cas/Backend.ts"
import { CasNodeInput, ContentId } from "../src/cas/Node.ts"
import { PathReadError, layerPathReader, type ReadPath } from "../src/cas/PathReader.ts"
import { CasStore, layerAddressSha256Live, layerFile } from "../src/cas/Store.ts"
import { makeMemoryFs } from "./MemoryFsHarness.ts"

const storeRoot = "published"

const node = (
  payload: ReadonlyArray<number>,
  tag: number,
  refs: CasNodeInput["refs"] = [],
): CasNodeInput => CasNodeInput.make({
  kind: { version: 0, tag },
  payload: Uint8Array.from(payload),
  refs,
})

it.effect("reads the layout the file backend writes — publish is a directory", () =>
  Effect.gen(function* () {
    const memory = yield* makeMemoryFs
    const writeLayer = layerFile(storeRoot).pipe(
      Layer.provide(Layer.mergeAll(
        Layer.succeed(FileSystem.FileSystem, memory.fs),
        layerAddressSha256Live,
      )),
    )
    // The "host": whatever ended up in the store root, served by path —
    // in production a git raw endpoint, here the harness filesystem
    // itself, absence mapped to None and failure to the typed error.
    const serve: ReadPath = (relativePath) =>
      memory.fs.readFile(`${storeRoot}/${relativePath}`).pipe(
        Effect.asSome,
        Effect.catchTag("PlatformError", (error) =>
          error.reason._tag === "NotFound"
            ? Effect.succeedNone
            : Effect.fail(new PathReadError({
                path: relativePath,
                reason: error.message,
              }))),
      )

    const child = node([1, 2, 3], 91)
    const id = yield* Effect.gen(function* () {
      const store = yield* CasStore
      const childId = yield* store.put(child)
      yield* store.put(node([4], 92, [{ expectedTag: 91, id: childId }]))
      return childId
    }).pipe(Effect.provide(writeLayer))

    yield* Effect.gen(function* () {
      const reader = yield* ByteReader
      const served = yield* reader.loadBytes(id)
      const held = yield* memory.dump
      expect(Option.isSome(served)).toBe(true)
      expect(served).toEqual(Option.fromNullishOr(
        held.get(`${storeRoot}/${objectRelativePath(id)}`)))

      const absent = ContentId.make("cd".repeat(32))
      expect(yield* reader.presence([id, absent])).toEqual(["present", "missing"])
    }).pipe(Effect.provide(layerPathReader(serve)))
  }))

it.effect("a host that cannot answer degrades typed, never silently", () => {
  const down: ReadPath = (relativePath) =>
    Effect.fail(new PathReadError({ path: relativePath, reason: "host down" }))

  return Effect.gen(function* () {
    const reader = yield* ByteReader
    const id = ContentId.make("ab".repeat(32))

    expect(yield* reader.presence([id, id])).toEqual(["failed", "failed"])

    const refused = yield* reader.loadBytes(id).pipe(Effect.flip)
    expect(refused._tag).toBe("CasBackendFailure")
    expect(refused.reason).toContain(objectRelativePath(id))
  }).pipe(Effect.provide(layerPathReader(down)))
})
