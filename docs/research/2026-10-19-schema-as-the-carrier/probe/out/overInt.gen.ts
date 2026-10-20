/**
 * faces: overInt, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"
import { type Int, plus } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<Int, never, never> = Effect.succeed(plus(9007199254740991, 1))
