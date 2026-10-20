/**
 * faces: failString, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"

export const main: Effect.Effect<never, string, never> = Effect.fail("bad")
