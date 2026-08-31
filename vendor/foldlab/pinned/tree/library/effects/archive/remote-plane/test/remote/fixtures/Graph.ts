/**
 * Deterministic seeded workload fixtures: content graphs.
 *
 * Generators produce production-shaped CAS graphs — history chains,
 * directory trees, shared-subtree diamonds, bulk fan-outs, duplicate-heavy
 * imports — as pure functions of (seed, params). Nodes are structural: each
 * names its children by index, never by digest, so generation is
 * digest-agnostic and the CONSUMING store computes every address at
 * admission time. A node's children always sit at strictly lower indices,
 * so ascending index order is a valid children-before-parents admission
 * order.
 *
 * Evidence class: G4 sampled evidence only. These fixtures model production
 * sync loads for exploratory and regression tests; they are NEVER a
 * substitute for the ratified conformance vectors under
 * `conformance/manifest`.
 */
import { Effect, Encoding } from "effect"
import type { CasError, ContentId, NodeKind } from "../../../src/cas/Node.ts"
import { CasNodeInput } from "../../../src/cas/Node.ts"
import { CasSchemeVersion, encodeCasNode, type CasStoreShape } from "../../../src/cas/Store.ts"
import { makeRng, type WorkloadRng } from "./Rng.ts"

/** Kind tag for payload-carrying leaves (blob-like content). */
export const leafKindTag = 1
/** Kind tag for interior nodes (directory or commit-like content). */
export const treeKindTag = 2

/** Payload size distribution. `maxPayloadBytes` bounds the PAYLOAD only;
 * callers align it with their configured budgets, remembering the canonical
 * frame adds 10 bytes plus 33 bytes per reference. */
export type PayloadProfile =
  | { readonly _tag: "smallMeta" }
  | { readonly _tag: "blob"; readonly maxPayloadBytes: number }
  | {
    readonly _tag: "mixed"
    readonly blobRatio: number
    readonly maxPayloadBytes: number
  }

/** Named graph shapes with their structural parameters. */
export type GraphShape =
  | { readonly _tag: "linearChain"; readonly length: number }
  | { readonly _tag: "tree"; readonly depth: number; readonly branching: number }
  | { readonly _tag: "diamond"; readonly sharedLeaves: number; readonly forks: number }
  | { readonly _tag: "wideFanout"; readonly width: number }
  | {
    readonly _tag: "duplicateHeavy"
    readonly leafSlots: number
    readonly dedupRatio: number
  }

/** One structural node: kind, payload bytes, children by index. */
export interface WorkloadNode {
  readonly kind: NodeKind
  readonly payload: Uint8Array
  readonly children: ReadonlyArray<number>
}

/** A generated workload graph. `nodes` is in admission order (children
 * before parents); `root` is always the last index. */
export interface WorkloadGraph {
  readonly name: string
  readonly seed: number
  readonly shape: GraphShape
  readonly nodes: ReadonlyArray<WorkloadNode>
  readonly root: number
}

const drawPayload = (rng: WorkloadRng, profile: PayloadProfile): Uint8Array => {
  switch (profile._tag) {
    case "smallMeta":
      return rng.bytes(rng.int(12, 64))
    case "blob": {
      const floor = Math.max(1, Math.ceil(profile.maxPayloadBytes / 2))
      return rng.bytes(rng.int(floor, profile.maxPayloadBytes))
    }
    case "mixed":
      return rng.fraction() < profile.blobRatio
        ? drawPayload(rng, { _tag: "blob", maxPayloadBytes: profile.maxPayloadBytes })
        : drawPayload(rng, { _tag: "smallMeta" })
  }
}

const nodeAt = (graph: WorkloadGraph, index: number): WorkloadNode => {
  const node = graph.nodes[index]
  if (node === undefined) {
    throw new Error(`workload graph ${graph.name} has no node at index ${index}`)
  }
  return node
}

interface Builder {
  readonly nodes: Array<WorkloadNode>
  readonly leaf: (payload: Uint8Array) => number
  readonly interior: (payload: Uint8Array, children: ReadonlyArray<number>) => number
}

const makeBuilder = (): Builder => {
  const nodes: Array<WorkloadNode> = []
  const push = (node: WorkloadNode): number => {
    for (const child of node.children) {
      if (child < 0 || child >= nodes.length) {
        throw new Error(`child index ${child} not below parent index ${nodes.length}`)
      }
    }
    nodes.push(node)
    return nodes.length - 1
  }
  return {
    nodes,
    leaf: (payload) => push({
      kind: { version: CasSchemeVersion, tag: leafKindTag },
      payload,
      children: [],
    }),
    interior: (payload, children) => push({
      kind: { version: CasSchemeVersion, tag: treeKindTag },
      payload,
      children: [...children],
    }),
  }
}

/** Generate one workload graph as a pure function of (seed, shape,
 * payload). Payload draws happen in node-emission order, so the same seed
 * regenerates the same bytes at every index. */
export const generateGraph = (options: {
  readonly seed: number
  readonly shape: GraphShape
  readonly payload: PayloadProfile
}): WorkloadGraph => {
  const { payload, seed, shape } = options
  const rng = makeRng(seed)
  const builder = makeBuilder()

  switch (shape._tag) {
    case "linearChain": {
      if (shape.length < 1) throw new Error("linearChain needs length >= 1")
      let previous = builder.leaf(drawPayload(rng, payload))
      for (let step = 1; step < shape.length; step += 1) {
        previous = builder.interior(drawPayload(rng, payload), [previous])
      }
      break
    }
    case "tree": {
      if (shape.depth < 0 || shape.branching < 1) {
        throw new Error("tree needs depth >= 0 and branching >= 1")
      }
      const build = (level: number): number => {
        if (level === 0) return builder.leaf(drawPayload(rng, payload))
        const children: Array<number> = []
        for (let slot = 0; slot < shape.branching; slot += 1) {
          children.push(build(level - 1))
        }
        return builder.interior(drawPayload(rng, payload), children)
      }
      build(shape.depth)
      break
    }
    case "diamond": {
      if (shape.sharedLeaves < 1 || shape.forks < 2) {
        throw new Error("diamond needs sharedLeaves >= 1 and forks >= 2")
      }
      const shared: Array<number> = []
      for (let slot = 0; slot < shape.sharedLeaves; slot += 1) {
        shared.push(builder.leaf(drawPayload(rng, payload)))
      }
      const forks: Array<number> = []
      for (let fork = 0; fork < shape.forks; fork += 1) {
        forks.push(builder.interior(drawPayload(rng, payload), shared))
      }
      builder.interior(drawPayload(rng, payload), forks)
      break
    }
    case "wideFanout": {
      if (shape.width < 1) throw new Error("wideFanout needs width >= 1")
      const children: Array<number> = []
      for (let slot = 0; slot < shape.width; slot += 1) {
        children.push(builder.leaf(drawPayload(rng, payload)))
      }
      builder.interior(drawPayload(rng, payload), children)
      break
    }
    case "duplicateHeavy": {
      if (shape.leafSlots < 1 || shape.dedupRatio < 0 || shape.dedupRatio > 1) {
        throw new Error("duplicateHeavy needs leafSlots >= 1 and dedupRatio in [0, 1]")
      }
      const distinct = Math.max(
        1,
        shape.leafSlots - Math.floor(shape.leafSlots * shape.dedupRatio),
      )
      const pool: Array<Uint8Array> = []
      const slots: Array<number> = []
      for (let slot = 0; slot < shape.leafSlots; slot += 1) {
        if (slot < distinct) {
          const fresh = drawPayload(rng, payload)
          pool.push(fresh)
          slots.push(builder.leaf(fresh))
        } else {
          const copied = pool[rng.int(0, pool.length - 1)]
          if (copied === undefined) throw new Error("duplicate pool is empty")
          slots.push(builder.leaf(copied.slice()))
        }
      }
      builder.interior(drawPayload(rng, payload), slots)
      break
    }
  }

  return {
    name: shape._tag,
    seed,
    shape,
    nodes: builder.nodes,
    root: builder.nodes.length - 1,
  }
}

/** Count structurally distinct nodes: two indices collapse to one stored
 * node exactly when kind, payload bytes, and (recursively distinct)
 * children coincide. This is the model-side prediction for how many
 * distinct addresses any conforming store admits for the graph. */
export const distinctNodeCount = (graph: WorkloadGraph): number => {
  const classes = new Map<string, number>()
  const classOf: Array<number> = []
  graph.nodes.forEach((node, index) => {
    const children = node.children.map((child) => {
      const klass = classOf[child]
      if (klass === undefined) throw new Error(`unclassified child ${child}`)
      return klass
    })
    const key = `${node.kind.version}.${node.kind.tag}:`
      + `${Encoding.encodeHex(node.payload)}:${children.join(",")}`
    const existing = classes.get(key)
    const klass = existing ?? classes.size
    if (existing === undefined) classes.set(key, klass)
    classOf[index] = klass
  })
  return classes.size
}

/** Resolve one structural node into a CasNodeInput, mapping child indices
 * to the addresses the consuming store already computed for them. */
export const resolveNode = (
  graph: WorkloadGraph,
  index: number,
  ids: ReadonlyArray<ContentId>,
): CasNodeInput => {
  const node = nodeAt(graph, index)
  return CasNodeInput.make({
    kind: { ...node.kind },
    payload: node.payload.slice(),
    refs: node.children.map((child) => {
      const id = ids[child]
      if (id === undefined) {
        throw new Error(`child ${child} of node ${index} has no admitted address yet`)
      }
      return { id, expectedTag: nodeAt(graph, child).kind.tag }
    }),
  })
}

/** Canonical bytes of one node once its children's addresses are known. */
export const canonicalBytesAt = (
  graph: WorkloadGraph,
  index: number,
  ids: ReadonlyArray<ContentId>,
): Uint8Array => encodeCasNode(resolveNode(graph, index, ids))

/** Admit a whole generated graph into any CasStore bottom-up (children
 * before parents, root last) and return the index-to-address map. The
 * store computes every address; the fixture never digests anything. */
export const admitGraphBottomUp = (
  store: CasStoreShape,
  graph: WorkloadGraph,
): Effect.Effect<ReadonlyArray<ContentId>, CasError> =>
  Effect.gen(function* () {
    const ids: Array<ContentId> = []
    for (let index = 0; index < graph.nodes.length; index += 1) {
      ids.push(yield* store.put(resolveNode(graph, index, ids)))
    }
    return ids
  })
