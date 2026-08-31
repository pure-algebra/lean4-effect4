/**
 * Graph laws over the read seam alone — closure enumeration and full
 * integrity verification, usable against any backend, read-only hosts
 * included. Content addressing makes the reachable graph a DAG; walks
 * emit children-first (a valid upload order) and deduplicate shared
 * children.
 *
 * `closure` decodes only far enough to follow references. `verify` is
 * the audit: every reachable node re-verified under the store law's
 * read checks — recomputed address, canonical decode, known kind — so
 * pointing it at an untrusted host answers exactly whether that host
 * faithfully serves the graph.
 */
import { Effect, Graph, Option } from "effect"
import {
  ByteReader,
  type BackendFailure,
  type ByteReaderShape,
} from "./Backend.ts"
import {
  ContentNotFound,
  DanglingReference,
  NonCanonicalBytes,
  StoreFailure,
  WrongKindReference,
  type CasError,
  type CasNodeInput,
  type ContentId,
} from "./Node.ts"
import { decodeCasNode } from "../internal/casCodec.ts"
import {
  AddressScheme,
  verifyNodeBytes,
  type CasAddress,
} from "./Store.ts"

const backendFailure = (failure: BackendFailure): StoreFailure =>
  new StoreFailure({
    reason: `Backend failed: ${failure.reason}`,
    cause: failure,
  })

/** Bytes at an id, absence typed: a missing root is `ContentNotFound`,
 * a missing child is the dangling reference it witnesses. */
const residentBytes = (
  reader: ByteReaderShape,
  id: ContentId,
  isRoot: boolean,
): Effect.Effect<Uint8Array, CasError> =>
  reader.loadBytes(id).pipe(
    Effect.mapError(backendFailure),
    Effect.flatMap((resident) => Option.match(resident, {
      onNone: () => Effect.fail<CasError>(isRoot
        ? new ContentNotFound({ id })
        : new DanglingReference({ missing: id })),
      onSome: (bytes) => Effect.succeed(bytes),
    })),
  )

const walkWith = (
  loadRefs: (
    reader: ByteReaderShape,
    id: ContentId,
    isRoot: boolean,
  ) => Effect.Effect<ReadonlyArray<ContentId>, CasError>,
  name: string,
) =>
  Effect.fn(name)(function* (root: ContentId) {
    const reader = yield* ByteReader
    const ordered: Array<ContentId> = []
    const pushed = new Set<ContentId>([root])
    interface Frame {
      readonly id: ContentId
      refs: ReadonlyArray<ContentId> | undefined
      next: number
    }
    const stack: Array<Frame> = [{ id: root, next: 0, refs: undefined }]

    while (stack.length > 0) {
      const frame = stack.at(-1)!
      if (frame.refs === undefined) {
        frame.refs = yield* loadRefs(reader, frame.id, ordered.length === 0
          && stack.length === 1)
      }
      if (frame.next < frame.refs.length) {
        const child = frame.refs[frame.next]!
        frame.next += 1
        if (!pushed.has(child)) {
          pushed.add(child)
          stack.push({ id: child, next: 0, refs: undefined })
        }
        continue
      }
      stack.pop()
      ordered.push(frame.id)
    }
    const walked: ReadonlyArray<ContentId> = ordered
    return walked
  })

/** Every id reachable from `root` through references, children-first
 * and deduplicated — root last. Decodes only far enough to follow
 * references; `verify` is the full audit. */
export const closure: (
  root: ContentId,
) => Effect.Effect<ReadonlyArray<ContentId>, CasError, ByteReader> = walkWith(
  (reader, id, isRoot) => residentBytes(reader, id, isRoot).pipe(
    Effect.flatMap((bytes) => Option.match(decodeCasNode(bytes), {
      onNone: () => Effect.fail(new NonCanonicalBytes({ id })),
      onSome: (node) => Effect.succeed(node.refs.map((ref) => ref.id)),
    })),
  ),
  "CasGraph.closure",
)

/** The audit under an explicit digest — the model quantifies over the
 * address function, and so does the walk. */
export const verifyWith = (
  address: CasAddress,
): (
  root: ContentId,
) => Effect.Effect<ReadonlyArray<ContentId>, CasError, ByteReader> =>
  Effect.fn("CasGraph.verify")(function* (root) {
    const reader = yield* ByteReader
    const pushed = new Set<ContentId>([root])
    const verified = new Map<ContentId, CasNodeInput>()
    const nodes = new Map<ContentId, Graph.IndexedNode<ContentId>>()
    const graph = Graph.beginMutation(Graph.directed<ContentId, number>())

    const graphNode = (id: ContentId): Graph.IndexedNode<ContentId> => {
      const resident = nodes.get(id)
      if (resident !== undefined) return resident
      const node = { index: Graph.addNode(graph, id), data: id }
      nodes.set(id, node)
      return node
    }

    const rootNode = graphNode(root)

    const loadVerified = (
      id: ContentId,
      isRoot: boolean,
    ): Effect.Effect<CasNodeInput, CasError> => {
      const cached = verified.get(id)
      if (cached !== undefined) return Effect.succeed(cached)
      return residentBytes(reader, id, isRoot).pipe(
        Effect.flatMap((bytes) => verifyNodeBytes(address, id, bytes)),
        Effect.tap((node) => Effect.sync(() => verified.set(id, node))),
      )
    }

    interface Frame {
      readonly id: ContentId
      node: CasNodeInput | undefined
      next: number
    }
    const stack: Array<Frame> = [{ id: root, next: 0, node: undefined }]

    while (stack.length > 0) {
      const frame = stack.at(-1)!
      if (frame.node === undefined) {
        frame.node = yield* loadVerified(
          frame.id,
          frame.id === root && stack.length === 1,
        )
      }
      if (frame.next < frame.node.refs.length) {
        const ref = frame.node.refs[frame.next]!
        frame.next += 1
        const child = yield* loadVerified(ref.id, false)
        if (child.kind.tag !== ref.expectedTag) {
          return yield* new WrongKindReference({
            ref: ref.id,
            expectedTag: ref.expectedTag,
            actualTag: child.kind.tag,
          })
        }
        Graph.addEdge(
          graph,
          graphNode(frame.id).index,
          graphNode(ref.id).index,
          ref.expectedTag,
        )
        if (!pushed.has(ref.id)) {
          pushed.add(ref.id)
          stack.push({ id: ref.id, next: 0, node: child })
        }
        continue
      }
      stack.pop()
    }

    const complete = Graph.endMutation(graph)
    const walked: ReadonlyArray<ContentId> = Array.from(
      Graph.values(Graph.dfsPostOrder(complete, { start: [rootNode.index] })),
    )
    return walked
  })

/** Re-verify every node reachable from `root` under the composition's
 * address scheme: recomputed address, canonical decode, known kind.
 * Succeeds with the children-first closure exactly when the backend
 * faithfully serves the whole graph. */
export const verify = (
  root: ContentId,
): Effect.Effect<
  ReadonlyArray<ContentId>,
  CasError,
  ByteReader | AddressScheme
> => AddressScheme.pipe(
  Effect.flatMap((address) => verifyWith(address)(root)),
)
