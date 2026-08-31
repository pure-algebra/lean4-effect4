/**
 * Deterministic seeded workload fixtures: peer preloading.
 *
 * Seeds the in-process reference peer with the remote-side subset of a
 * generated graph through the peer's existing `ScenarioRealization.nodes`
 * seam. Addresses and canonical bytes come from a scratch instance of the
 * real in-memory store — the consuming-store principle: the fixture never
 * digests anything itself.
 *
 * Evidence class: G4 sampled evidence only. These fixtures model production
 * sync loads for exploratory and regression tests; they are NEVER a
 * substitute for the ratified conformance vectors under
 * `conformance/manifest`.
 */
import { Effect } from "effect"
import type { Crypto, Scope } from "effect"
import type { CasError, ContentId } from "../../../src/cas/Node.ts"
import { makeMemoryCasStore, makeSha256Address } from "../../../src/cas/Store.ts"
import type { PeerEndpoint } from "../harness/ConformancePeer.ts"
import { ReferencePeer } from "../harness/ReferencePeer.ts"
import { admitGraphBottomUp, canonicalBytesAt, type WorkloadGraph } from "./Graph.ts"

export interface PeerSeed {
  /** Index-to-address map for the WHOLE graph, computed by a scratch run
   * of the real in-memory store. */
  readonly ids: ReadonlyArray<ContentId>
  /** Canonical bytes for the seeded subset, keyed by address — the shape
   * `ScenarioRealization.nodes` accepts. */
  readonly nodes: ReadonlyMap<string, Uint8Array>
}

/** Compute the peer preload for a downward-closed subset of the graph. A
 * subset holding a parent without one of its children is a fixture defect
 * and dies: a conforming remote never holds a partial parent. */
export const seedPeerNodes = (
  graph: WorkloadGraph,
  subset: ReadonlyArray<number>,
): Effect.Effect<PeerSeed, CasError, Crypto.Crypto> =>
  Effect.gen(function* () {
    const chosen = new Set(subset)
    for (const index of chosen) {
      const node = graph.nodes[index]
      if (node === undefined) {
        return yield* Effect.die(new Error(`subset names missing index ${index}`))
      }
      for (const child of node.children) {
        if (!chosen.has(child)) {
          return yield* Effect.die(new Error(
            `subset is not downward-closed: ${index} held without child ${child}`,
          ))
        }
      }
    }

    const address = yield* makeSha256Address
    const scratch = yield* makeMemoryCasStore(address)
    const ids = yield* admitGraphBottomUp(scratch, graph)

    const nodes = new Map<string, Uint8Array>()
    for (const index of [...chosen].sort((left, right) => left - right)) {
      const id = ids[index]
      if (id === undefined) {
        return yield* Effect.die(new Error(`no admitted address for index ${index}`))
      }
      nodes.set(id, canonicalBytesAt(graph, index, ids))
    }
    return { ids, nodes }
  })

/** Serve the reference peer already holding the given subset. */
export const serveSeededReference = (
  graph: WorkloadGraph,
  subset: ReadonlyArray<number>,
): Effect.Effect<
  { readonly endpoint: PeerEndpoint; readonly seed: PeerSeed },
  CasError,
  Crypto.Crypto | Scope.Scope
> =>
  Effect.gen(function* () {
    const seed = yield* seedPeerNodes(graph, subset)
    const endpoint = yield* ReferencePeer.serve({ nodes: seed.nodes })
    return { endpoint, seed }
  })
