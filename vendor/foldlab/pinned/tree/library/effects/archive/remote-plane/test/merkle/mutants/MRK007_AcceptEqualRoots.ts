import { Equal } from "effect"
import { verifyConsistency } from "../../../src/internal/merkleConsistency.ts"
import type { ConsistencyFunction } from "../MerkleFixtures.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a consistency verifier that shortcuts on equal roots without reconstructing — a relation claimed by identity instead of proved by the size-derived rebuild."

/** Accept equal roots without running the size-derived reconstruction. */
export const mutantVerify: ConsistencyFunction = (input) =>
  Equal.equals(input.oldRoot, input.newRoot) || verifyConsistency(input)
