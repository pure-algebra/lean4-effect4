/**
 * faces: successPair, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"
import { pair } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<readonly [number, "x"], never, never> = Effect.succeed(pair(1, "x"))
