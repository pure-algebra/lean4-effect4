/**
 * faces: successMap, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"
import { mapEmpty, mapSet } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<Readonly<Record<string, number>>, never, never> = Effect.succeed(
  mapSet(mapEmpty(), "k", 1)
)
