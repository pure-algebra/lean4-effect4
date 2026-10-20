/**
 * faces: successIntNonNegative, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"
import { type Int, minus } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<Int, never, never> = Effect.succeed(minus(3, 1))
