/**
 * The first on-disk CAS: the file backend over a real filesystem, fed
 * the Lean conformance vectors. Where `FileBackend.test.ts` proves the
 * backend contract against the pure in-memory `FileSystem` harness,
 * this suite proves the end-to-end claim: a durable store on actual
 * disk whose object files are byte-for-byte the canonical encoding,
 * addressed by the Lean-computed digests, readable by a completely
 * fresh composition over the same directory.
 *
 * The real-disk `FileSystem` realization is the platform-node layer
 * (`fixtures/diskFs.ts`), shared with every suite that exercises the
 * on-disk store; disk-side assertions go through the same `FileSystem`
 * service the backend composes over.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Encoding, FileSystem } from "effect"
import { Cas } from "../src/index.ts"
import { bytesOnDisk, layerDisk, withStoreRoot } from "./fixtures/diskFs.ts"
import { loadVectors } from "./fixtures/vectors.ts"

const { ConformanceVector, Loader, RootStore, Store } = Cas
const { toNodeInput } = ConformanceVector

/** Replay every vector word binding by binding, asserting each returned
 * id equals the Lean-computed address. Answers the loaded fixtures for
 * further assertions. */
const replayVectors = Effect.gen(function* () {
  const { index, vectors } = yield* loadVectors
  expect(vectors.length).toBeGreaterThan(0)
  const store = yield* Store
  for (const vector of vectors) {
    for (const [position, binding] of vector.word.entries()) {
      const id = yield* store.put(toNodeInput(binding.node))
      expect(`${vector.name}[${position}] ${id}`)
        .toBe(`${vector.name}[${position}] ${binding.address}`)
    }
  }
  return { index, vectors }
})

it.effect("replay: every Lean vector lands on disk at its Lean-computed address", () =>
  withStoreRoot((storeRoot) =>
    replayVectors.pipe(Effect.provide(layerDisk(storeRoot)))))

it.effect("layout: every object file is exactly the canonical encoding", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const { vectors } = yield* replayVectors
      for (const vector of vectors) {
        for (const [position, binding] of vector.word.entries()) {
          const label = `${vector.name}[${position}]`
          const path =
            `${storeRoot}/${Cas.objectRelativePath(binding.address)}`
          const fs = yield* FileSystem.FileSystem
          expect(`${label} ${yield* fs.exists(path)}`).toBe(`${label} true`)
          // The disk representation is the canonical encoding of the
          // node — byte for byte, nothing else.
          const resident = yield* bytesOnDisk(path)
          expect(`${label} ${Encoding.encodeHex(resident)}`)
            .toBe(`${label} ${
              Encoding.encodeHex(Cas.encodeNode(toNodeInput(binding.node)))
            }`)
        }
      }
    }).pipe(Effect.provide(layerDisk(storeRoot)))))

it.effect("persistence: a fresh composition over the same directory serves every root", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const { index, vectors } = yield* replayVectors.pipe(
        Effect.provide(layerDisk(storeRoot)),
      )
      // A completely fresh layer stack over the same directory: only
      // the bytes on disk carry the store across.
      yield* Effect.gen(function* () {
        const loader = yield* Loader
        for (const [position, entry] of index.vectors.entries()) {
          const rootBinding =
            vectors[position]!.word[vectors[position]!.word.length - 1]!
          const resident = yield* loader.load(entry.root)
          expect(`${entry.name} ${Encoding.encodeHex(resident.payload)}`)
            .toBe(`${entry.name} ${
              Encoding.encodeHex(rootBinding.node.payload)
            }`)
          expect(resident.refs).toEqual(rootBinding.node.refs)
        }
      }).pipe(Effect.provide(layerDisk(storeRoot)))
    })))

it.effect("idempotence: a second replay answers the same ids and moves no bytes", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const { vectors } = yield* replayVectors
      const objectPath = (id: Cas.ContentId): string =>
        `${storeRoot}/${Cas.objectRelativePath(id)}`
      const snapshot = new Map<string, string>()
      for (const vector of vectors) {
        for (const binding of vector.word) {
          snapshot.set(
            objectPath(binding.address),
            Encoding.encodeHex(yield* bytesOnDisk(objectPath(binding.address))),
          )
        }
      }
      // The second replay: every put answers the same id (asserted
      // inside the replay) via the already-resident branch.
      yield* replayVectors
      for (const [path, before] of snapshot) {
        const after = Encoding.encodeHex(yield* bytesOnDisk(path))
        expect(`${path} ${after}`).toBe(`${path} ${before}`)
      }
    }).pipe(Effect.provide(layerDisk(storeRoot)))))

it.effect("roots: publishing a vector root lands the empty file under roots/", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const { index } = yield* replayVectors
      const roots = yield* RootStore
      const fs = yield* FileSystem.FileSystem
      for (const entry of index.vectors) {
        yield* roots.publish(entry.root)
        const path = `${storeRoot}/${Cas.rootRelativePath(entry.root)}`
        expect(`${entry.name} ${yield* fs.exists(path)}`)
          .toBe(`${entry.name} true`)
        expect((yield* bytesOnDisk(path)).byteLength).toBe(0)
      }
      const published = yield* roots.list
      expect([...published].sort())
        .toEqual([...new Set(index.vectors.map((entry) => entry.root))].sort())
    }).pipe(Effect.provide(layerDisk(storeRoot)))))
