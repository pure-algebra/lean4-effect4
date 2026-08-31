/**
 * The library used as a user, over real disk: the typed surfaces —
 * value projections with typed references, recipe-1 blobs, graph
 * closure and audit, and closure-ordered store-to-store transfer —
 * exercised end to end over the same on-disk composition
 * `FileCas.test.ts` proved at the byte plane. Every law here reads
 * through a composition whose only carrier is the object files under
 * a temp store root.
 *
 * Transfer note: the library ships no store-to-store transfer
 * service. The transfer lane therefore pushes the way the push law
 * itself does: children-first closure enumeration plus per-node puts,
 * asserting the ids and bytes land identically in the second store.
 */
import { expect, it } from "@effect/vitest"
import { cast, Effect, FileSystem, Layer, Schema, Stream } from "effect"
import { Cas } from "../src/index.ts"
import { bytesOnDisk, layerDisk, withStoreRoot } from "./fixtures/diskFs.ts"
import { loadVectors } from "./fixtures/vectors.ts"

/** The disk composition with the address scheme kept visible, so the
 * graph audit (`Cas.Graph.verify`) can recompute every address. */
const layerDiskVerified = (storeRoot: string) =>
  Layer.mergeAll(layerDisk(storeRoot), Cas.layerAddressSha256Live)

/** The blob service over the disk store, seams still exposed. */
const layerDiskBlob = (storeRoot: string) =>
  Cas.Blob.layer.pipe(Layer.provideMerge(layerDisk(storeRoot)))

// ---------------------------------------------------------------------------
// The typed projections under test: a child value and a parent whose
// schema carries typed references (CAS-005) — one direct edge and a
// list of same-kind edges for depth and sharing.

interface Author {
  readonly name: string
  readonly year: number
}
const AuthorValue = Cas.value({
  kindTag: 0x61,
  revision: 0,
  schema: Schema.Struct({ name: Schema.String, year: Schema.Int }),
})

interface Post {
  readonly title: string
  readonly author: Cas.Root<Author>
  readonly related: ReadonlyArray<Cas.Root<Post>>
}
const PostValue: Cas.Value<Post> = Cas.value({
  kindTag: 0x62,
  revision: 0,
  schema: Schema.Struct({
    author: Cas.ref(() => AuthorValue),
    related: Schema.Array(Cas.ref((): Cas.Value<Post> => PostValue)),
    title: Schema.String,
  }),
})

/** A four-node DAG with a shared leaf: author under three posts, posts
 * chained by `related` edges. Built leaf-up, as the admission law
 * requires. */
const buildPostGraph = Effect.gen(function* () {
  const author = yield* AuthorValue.put({ name: "hopper", year: 1906 })
  const first = yield* PostValue.put({ author, related: [], title: "first" })
  const second = yield* PostValue.put({ author, related: [first], title: "second" })
  const top = yield* PostValue.put({ author, related: [first, second], title: "top" })
  return { author, first, second, top }
})

/** Deterministic non-repeating byte pattern for blob content. */
const patternBytes = (length: number): Uint8Array => {
  const bytes = new Uint8Array(length)
  for (let index = 0; index < length; index += 1) {
    bytes[index] = index % 251
  }
  return bytes
}

// ---------------------------------------------------------------------------
// 1. VALUE — typed persistence and the leaf-up law.

it.effect("value: typed roots persist — a fresh composition serves parent and child", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const written = yield* Effect.gen(function* () {
        const author = yield* AuthorValue.put({ name: "hopper", year: 1906 })
        const post = yield* PostValue.put({ author, related: [], title: "compilers" })
        return { author, post }
      }).pipe(Effect.provide(layerDisk(storeRoot)))

      // A completely fresh layer stack over the same directory: only
      // the object files carry the typed values across.
      yield* Effect.gen(function* () {
        const post = yield* PostValue.get(written.post)
        expect(post.title).toBe("compilers")
        // The reference decodes lazily to the typed root, not a child.
        expect(post.author).toBe(written.author)
        const author = yield* AuthorValue.get(post.author)
        expect(author).toEqual({ name: "hopper", year: 1906 })
      }).pipe(Effect.provide(layerDisk(storeRoot)))
    })))

it.effect("value: a put whose ref target is absent refuses with DanglingReference", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const absent: Cas.Root<Author> = cast(Cas.ContentId.make("ab".repeat(32)))
      const error = yield* PostValue.put({
        author: absent,
        related: [],
        title: "nowhere",
      }).pipe(Effect.flip)
      expect(error._tag).toBe("CasError/DanglingReference")
    }).pipe(Effect.provide(layerDisk(storeRoot)))))

// ---------------------------------------------------------------------------
// 2. BLOB — recipe-1 construction and verified read over disk.

it.effect("blob: a multi-chunk blob round-trips verified, every graph node a real object file", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      // Three leaves: two full 65,536-byte chunks and one 1,234-byte tail.
      const content = patternBytes(Cas.Blob.ChunkSize * 2 + 1234)
      const blobRef = yield* Cas.Blob.put(Stream.succeed(content)).pipe(
        Effect.provide(layerDiskBlob(storeRoot)),
      )

      // Verified read through a fresh composition over the same directory.
      yield* Effect.gen(function* () {
        const info = yield* Cas.Blob.inspect(blobRef)
        expect(info.recipeId).toBe(Cas.Blob.ReferencedChunkRecipe)
        expect(info.totalBytes).toBe(BigInt(content.length))
        expect(info.leafCount).toBe(3)

        const restored = yield* Cas.Blob.get(blobRef)
        expect(restored).toEqual(content)

        // The blob is an ordinary node graph: 3 chunks + 3 leaves +
        // 2 parents + 1 manifest, each resident as an object file.
        const ids = yield* Cas.Graph.closure(blobRef)
        expect(ids.length).toBe(9)
        expect(ids.at(-1)).toBe(blobRef)
        const fs = yield* FileSystem.FileSystem
        for (const id of ids) {
          const path = `${storeRoot}/${Cas.objectRelativePath(id)}`
          expect(`${id} ${yield* fs.exists(path)}`).toBe(`${id} true`)
        }
      }).pipe(Effect.provide(layerDiskBlob(storeRoot)))
    })), 30_000)
// The multi-chunk round trip is real disk IO twice over (write path,
// then a fresh verified read composition) and measures ~5.3s on a
// contended host against vitest's 5s default — a timeout raise on
// exactly this test, assertions untouched (the entity-store-generate
// precedent: a gate red for reasons unrelated to what it asserts).

// ---------------------------------------------------------------------------
// 3. GRAPH — children-first closure and the audit, honest and tampered.

it.effect("graph: closure is children-first and the audit passes over the disk store", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const { top } = yield* buildPostGraph
      const ids = yield* Cas.Graph.closure(top)

      // Deduplicated, root last.
      expect(new Set(ids).size).toBe(ids.length)
      expect(ids.at(-1)).toBe(top)
      expect(ids.length).toBe(4)

      // The children-first property asserted directly over the order:
      // every reference of the node at position k resolves among the
      // ids before position k.
      const loader = yield* Cas.Loader
      const seen = new Set<Cas.ContentId>()
      for (const id of ids) {
        const node = yield* loader.load(id)
        for (const reference of node.refs) {
          expect(`${id} -> ${reference.id} ${seen.has(reference.id)}`)
            .toBe(`${id} -> ${reference.id} true`)
        }
        seen.add(id)
      }

      // The full audit re-verifies every node and answers the same order.
      const audited = yield* Cas.Graph.verify(top)
      expect(audited).toEqual(ids)
    }).pipe(Effect.provide(layerDiskVerified(storeRoot)))))

it.effect("graph: the audit refuses a store whose object bytes were swapped", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const { author, top } = yield* buildPostGraph.pipe(
        Effect.provide(layerDisk(storeRoot)),
      )

      // The untrusted host swaps the child's object file for the
      // canonical encoding of a different node — canonical bytes, known
      // kind, wrong address. The audit must answer AddressMismatch.
      const forged = Cas.encodeNode(Cas.NodeInput.make({
        kind: { version: Cas.SchemeVersion, tag: 0x61 },
        payload: new Uint8Array([1, 2, 3]),
        refs: [],
      }))
      const path = `${storeRoot}/${Cas.objectRelativePath(author)}`
      const fs = yield* FileSystem.FileSystem
      yield* fs.writeFile(path, forged)

      yield* Effect.gen(function* () {
        const error = yield* Cas.Graph.verify(top).pipe(Effect.flip)
        expect(error._tag).toBe("CasError/AddressMismatch")
      }).pipe(Effect.provide(layerDiskVerified(storeRoot)))
    })))

// ---------------------------------------------------------------------------
// 4. TRANSFER — closure-ordered store-to-store push, the push law by
// hand: children-first enumeration, per-node puts.

it.effect("transfer: closure-ordered push carries a graph store-to-store byte-identically", () =>
  withStoreRoot((rootA) =>
    withStoreRoot((rootB) =>
      Effect.gen(function* () {
        // Store A: build the graph and enumerate it children-first.
        const { nodes, top } = yield* Effect.gen(function* () {
          const built = yield* buildPostGraph
          const ids = yield* Cas.Graph.closure(built.top)
          const loader = yield* Cas.Loader
          const loaded = yield* Effect.forEach(ids, (id) =>
            loader.load(id).pipe(Effect.map((node) => ({ id, node }))))
          return { nodes: loaded, top: built.top }
        }).pipe(Effect.provide(layerDisk(rootA)))

        // Store B: replay the closure in order. Every put must land on
        // the same content id — the transfer is identity-preserving.
        yield* Effect.gen(function* () {
          const store = yield* Cas.Store
          for (const { id, node } of nodes) {
            const landed = yield* store.put(node)
            expect(landed).toBe(id)
          }
          const audited = yield* Cas.Graph.verify(top)
          expect(audited.length).toBe(nodes.length)
          const decoded = yield* PostValue.get(top)
          expect(decoded.title).toBe("top")
        }).pipe(Effect.provide(layerDiskVerified(rootB)))

        // Byte identity on disk: the same id names the same bytes in
        // both stores.
        for (const { id } of nodes) {
          const relative = Cas.objectRelativePath(id)
          const inA = yield* bytesOnDisk(`${rootA}/${relative}`)
          const inB = yield* bytesOnDisk(`${rootB}/${relative}`)
          expect(inB).toEqual(inA)
        }
      }))))

// ---------------------------------------------------------------------------
// 5. CORRUPTION HALF-LAW — read verification on real disk.

it.effect("corruption: a tampered object file refuses the verified load with AddressMismatch", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const { vectors } = yield* loadVectors
      const vector = vectors[0]!
      const rootBinding = vector.word[vector.word.length - 1]!

      // Replay one Lean vector word into the fresh store.
      yield* Effect.gen(function* () {
        const store = yield* Cas.Store
        for (const binding of vector.word) {
          const id = yield* store.put(Cas.ConformanceVector.toNodeInput(binding.node))
          expect(id).toBe(binding.address)
        }
      }).pipe(Effect.provide(layerDisk(storeRoot)))

      // Overwrite the root's object file with different canonical
      // bytes: same kind, payload grown by one byte, same references.
      const original = Cas.ConformanceVector.toNodeInput(rootBinding.node)
      const tampered = Cas.encodeNode(Cas.NodeInput.make({
        kind: original.kind,
        payload: Uint8Array.from([...original.payload, 0]),
        refs: original.refs,
      }))
      const path = `${storeRoot}/${Cas.objectRelativePath(rootBinding.address)}`
      const fs = yield* FileSystem.FileSystem
      yield* fs.writeFile(path, tampered)

      // The verified load path over a fresh composition refuses typed.
      yield* Effect.gen(function* () {
        const loader = yield* Cas.Loader
        const error = yield* loader.load(rootBinding.address).pipe(Effect.flip)
        expect(error._tag).toBe("CasError/AddressMismatch")
      }).pipe(Effect.provide(layerDisk(storeRoot)))
    })))
