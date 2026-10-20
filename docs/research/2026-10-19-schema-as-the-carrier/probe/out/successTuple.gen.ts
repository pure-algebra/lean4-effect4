/**
 * faces: successTuple, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"
import { tuple } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<readonly [number, "a", boolean], never, never> = Effect.succeed(tuple(1, "a", false))
