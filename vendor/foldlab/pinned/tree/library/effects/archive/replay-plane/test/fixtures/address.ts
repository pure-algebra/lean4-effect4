/** Deterministic CAS addressing for tests, one home.
 *
 * `deterministicAddress` hands out sequential content-keyed ids;
 * `trackingAddress` additionally observes replay artifacts as the store
 * admits them — history chaining under the history tag and decoded
 * witnesses under the witness tag. The per-file copies these replace had
 * quietly diverged in what they collected. */
import { Effect, Encoding, Option, Schema } from "effect"
import { ContentId } from "../../src/cas/Node.ts"
import { decodeCasNode, type CasAddress } from "../../src/cas/Store.ts"
import { HistoryKindTag, WitnessKindTag } from "../../src/internal/kindTags.ts"
import { decodeWitness, StoredWitness } from "../../src/internal/storage.ts"

export { HistoryKindTag, WitnessKindTag }

export const deterministicAddress = (): CasAddress => {
  const ids = new Map<string, ContentId>()
  let next = 1n
  return {
    digest: (bytes) => Effect.sync(() => {
      const key = Encoding.encodeHex(bytes)
      const resident = ids.get(key)
      if (resident !== undefined) return resident
      const id = ContentId.make((next++).toString(16).padStart(64, "0"))
      ids.set(key, id)
      return id
    }),
  }
}

export interface TrackingAddress {
  readonly address: CasAddress
  readonly latestHistory: () => ContentId | undefined
  readonly historyDepth: (root: ContentId) => number
  readonly witnesses: () => ReadonlyArray<StoredWitness>
  readonly witnessedOutcomes: () => ReadonlyArray<StoredWitness["outcome"]>
  readonly witnessIds: () => ReadonlyArray<ContentId>
}

export const trackingAddress = (): TrackingAddress => {
  const ids = new Map<string, ContentId>()
  const historyParents = new Map<ContentId, ContentId | undefined>()
  const witnesses: Array<StoredWitness> = []
  const witnessedOutcomes: Array<StoredWitness["outcome"]> = []
  const witnessIds: Array<ContentId> = []
  let next = 1n
  let latestHistory: ContentId | undefined
  return {
    address: {
      digest: (canonicalBytes) =>
        Effect.sync(() => {
          const key = Encoding.encodeHex(canonicalBytes)
          const resident = ids.get(key)
          if (resident !== undefined) return resident
          const id = ContentId.make((next++).toString(16).padStart(64, "0"))
          ids.set(key, id)
          const decoded = Option.getOrUndefined(decodeCasNode(canonicalBytes))
          if (decoded?.kind.tag === HistoryKindTag) {
            latestHistory = id
            historyParents.set(id, decoded.refs[0]?.id)
          }
          if (decoded?.kind.tag === WitnessKindTag) {
            const witness = Schema.decodeUnknownSync(StoredWitness)(
              decodeWitness(decoded.payload),
            )
            witnesses.push(witness)
            witnessedOutcomes.push(witness.outcome)
            witnessIds.push(id)
          }
          return id
        }),
    },
    latestHistory: () => latestHistory,
    historyDepth: (root) => {
      let depth = 0
      let current: ContentId | undefined = root
      const seen = new Set<ContentId>()
      while (current !== undefined && !seen.has(current)) {
        seen.add(current)
        depth += 1
        current = historyParents.get(current)
      }
      return depth
    },
    witnesses: () => witnesses,
    witnessedOutcomes: () => witnessedOutcomes,
    witnessIds: () => witnessIds,
  }
}
