import { decodeOpening } from "../../../src/internal/merkleProofCodec.ts"
import type { OpeningDecodeFunction } from "../MerkleFixtures.ts"

export const represents = "Killing this mutant demonstrates the vectors notice an opening decoder that accepts truncated documents by padding them — proof material parsed open instead of fail-closed."

/** Zero-pad documents shorter than the twelve-byte header. */
export const mutantDecode: OpeningDecodeFunction = (bytes) =>
  decodeOpening(bytes.length < 12
    ? [...bytes, ...Array.from({ length: 12 - bytes.length }, () => 0)]
    : bytes)
