import type { ChunkFunction } from "../MerkleFixtures.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a chunker that loses bytes — chunking must be a lossless declared partition, with one root per recipe and content."

/** Silently drop the final chunk. */
export const mutantChunk: ChunkFunction = (recipe, bytes) =>
  recipe.chunk(bytes).slice(0, -1)
