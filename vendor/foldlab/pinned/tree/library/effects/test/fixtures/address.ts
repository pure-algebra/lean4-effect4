/** Deterministic CAS addressing for tests, one home: sequential
 * content-keyed ids, equal bytes always answering the equal id. The
 * replay-observing `trackingAddress` variant rides with the stashed
 * plane at `archive/replay-plane/test/fixtures/address.ts`. */
import { Effect, Encoding } from "effect"
import { ContentId } from "../../src/cas/Node.ts"
import type { CasAddress } from "../../src/cas/Store.ts"

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
