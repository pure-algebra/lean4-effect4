/**
 * faces: failNat, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"

export const main: Effect.Effect<never, number, never> = Effect.fail(3)
