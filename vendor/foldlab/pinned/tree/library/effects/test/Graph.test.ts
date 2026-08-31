/**
 * The graph laws: children-first deduplicated closure over any reader,
 * and verify as the untrusted-host audit — a host that hides or
 * corrupts a node is refused typed, at the node that witnesses it.
 */
import { expect, it } from "@effect/vitest"
import { Effect, FileSystem, Layer } from "effect"
import { ByteReader, makeMemoryBackend, objectRelativePath } from "../src/cas/Backend.ts"
import { closure, verify, verifyWith } from "../src/cas/Graph.ts"
import { CasNodeInput, ContentId } from "../src/cas/Node.ts"
import { PathReadError, layerPathReader, type ReadPath } from "../src/cas/PathReader.ts"
import {
  CasStore,
  encodeCasNode,
  layerAddressSha256Live,
  layerFile,
  layerMemoryLive,
} from "../src/cas/Store.ts"
import { makeMemoryFs, type MemoryFs } from "./MemoryFsHarness.ts"
import { deterministicAddress } from "./fixtures/address.ts"

const node = (
  payload: ReadonlyArray<number>,
  tag: number,
  refs: CasNodeInput["refs"] = [],
): CasNodeInput => CasNodeInput.make({
  kind: { version: 0, tag },
  payload: Uint8Array.from(payload),
  refs,
})

/** Seed the diamond: root → left,right; both → shared child. */
const seedDiamond = Effect.gen(function* () {
  const store = yield* CasStore
  const child = yield* store.put(node([1], 91))
  const left = yield* store.put(node([2], 92, [{ expectedTag: 91, id: child }]))
  const right = yield* store.put(node([3], 92, [{ expectedTag: 91, id: child }]))
  const root = yield* store.put(node([4], 93, [
    { expectedTag: 92, id: left },
    { expectedTag: 92, id: right },
  ]))
  return { child, left, right, root }
})

it.effect("closure is children-first, deduplicated, root last", () =>
  Effect.gen(function* () {
    const graph = yield* seedDiamond
    const ordered = yield* closure(graph.root)

    expect(ordered.length).toBe(4)
    expect(ordered[0]).toBe(graph.child)
    expect(ordered.at(-1)).toBe(graph.root)
    // Children-first everywhere: every reference points backward.
    expect(ordered.indexOf(graph.left)).toBeGreaterThan(ordered.indexOf(graph.child))
    expect(ordered.indexOf(graph.right)).toBeGreaterThan(ordered.indexOf(graph.child))

    // verify walks the same closure, fully re-verified.
    expect(yield* verify(graph.root)).toEqual(ordered)
  }).pipe(Effect.provide(layerMemoryLive)))

const storeRoot = "published"

const hostOver = (
  memory: MemoryFs,
  hidden?: string,
): ReadPath => (relativePath) =>
  relativePath === hidden
    ? Effect.succeedNone
    : memory.fs.readFile(`${storeRoot}/${relativePath}`).pipe(
        Effect.asSome,
        Effect.catchTag("PlatformError", (error) =>
          error.reason._tag === "NotFound"
            ? Effect.succeedNone
            : Effect.fail(new PathReadError({
                path: relativePath,
                reason: error.message,
              }))),
      )

it.effect("verify audits an untrusted host: hidden and corrupted nodes refuse typed", () =>
  Effect.gen(function* () {
    const memory = yield* makeMemoryFs
    const writeLayer = layerFile(storeRoot).pipe(
      Layer.provide(Layer.mergeAll(
        Layer.succeed(FileSystem.FileSystem, memory.fs),
        layerAddressSha256Live,
      )),
    )
    const graph = yield* seedDiamond.pipe(Effect.provide(writeLayer))

    // The faithful host verifies whole.
    const audited = yield* verify(graph.root).pipe(
      Effect.provide([layerPathReader(hostOver(memory)), layerAddressSha256Live]),
    )
    expect(audited.length).toBe(4)

    // A host hiding the shared child is refused at the reference that
    // witnesses it.
    const hiding = yield* verify(graph.root).pipe(
      Effect.provide([
        layerPathReader(hostOver(memory, objectRelativePath(graph.child))),
        layerAddressSha256Live,
      ]),
      Effect.flip,
    )
    expect(hiding._tag).toBe("CasError/DanglingReference")
    expect(hiding._tag === "CasError/DanglingReference" ? hiding.missing : undefined)
      .toBe(graph.child)

    // A host serving corrupted bytes is refused at the recomputed
    // address.
    const path = `${storeRoot}/${objectRelativePath(graph.child)}`
    const corrupted = (yield* memory.dump).get(path)!.slice()
    corrupted[6] = corrupted[6] === 0 ? 1 : 0
    yield* memory.poke(path, corrupted)
    const refused = yield* verify(graph.root).pipe(
      Effect.provide([layerPathReader(hostOver(memory)), layerAddressSha256Live]),
      Effect.flip,
    )
    expect(refused._tag).toBe("CasError/AddressMismatch")
  }))

it.effect("verify checks a shared child's expected tag on every incoming edge", () =>
  Effect.gen(function* () {
    const address = deterministicAddress()
    const backend = makeMemoryBackend()
    const admitRaw = (value: CasNodeInput) => Effect.gen(function* () {
      const bytes = encodeCasNode(value)
      const id = yield* address.digest(bytes)
      yield* backend.writer.putBytes(id, bytes)
      return id
    })

    const child = yield* admitRaw(node([1], 91))
    const left = yield* admitRaw(node([2], 92, [{ expectedTag: 91, id: child }]))
    const right = yield* admitRaw(node([3], 92, [{ expectedTag: 90, id: child }]))
    const root = yield* admitRaw(node([4], 93, [
      { expectedTag: 92, id: left },
      { expectedTag: 92, id: right },
    ]))

    const error = yield* verifyWith(address)(root).pipe(
      Effect.provideService(ByteReader, backend.reader),
      Effect.flip,
    )
    expect(error).toMatchObject({
      _tag: "CasError/WrongKindReference",
      ref: child,
      expectedTag: 90,
      actualTag: 91,
    })
  }))
