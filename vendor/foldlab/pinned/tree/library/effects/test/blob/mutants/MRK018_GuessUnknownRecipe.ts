import { Option } from "effect"
import type { CasBlob } from "../../../src/cas/Blob.ts"

/**
 * Killing this mutant demonstrates the vectors notice a manifest reader that accepts an unregistered recipe identifier instead of failing closed — a reader guessing blob semantics it was never taught.
 */
export const mutantDecode = (
  bytes: Uint8Array,
): Option.Option<CasBlob.ManifestContent> => {
  if (bytes.length !== 16) return Option.none()
  const recipeId = (bytes[0] ?? 0) * 0x1000000
    + (bytes[1] ?? 0) * 0x10000
    + (bytes[2] ?? 0) * 0x100
    + (bytes[3] ?? 0)
  let totalBytes = 0n
  for (let index = 4; index < 12; index += 1) {
    totalBytes = (totalBytes << 8n) | BigInt(bytes[index] ?? 0)
  }
  const leafCount = (bytes[12] ?? 0) * 0x1000000
    + (bytes[13] ?? 0) * 0x10000
    + (bytes[14] ?? 0) * 0x100
    + (bytes[15] ?? 0)
  return Option.some({ recipeId, totalBytes, leafCount })
}
