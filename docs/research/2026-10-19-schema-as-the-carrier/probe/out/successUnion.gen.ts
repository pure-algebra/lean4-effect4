/**
 * faces: successUnion, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"
import { ifCase } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<number | string, never, never> = ifCase(
  () => true,
  () => Effect.succeed(1),
  () => Effect.succeed("x")
)
