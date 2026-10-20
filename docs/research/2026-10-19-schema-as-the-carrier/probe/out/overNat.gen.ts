/**
 * faces: overNat, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"
import { add } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<number, never, never> = Effect.succeed(add(9007199254740991, 2))
