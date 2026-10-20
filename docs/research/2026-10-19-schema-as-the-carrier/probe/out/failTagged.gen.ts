/**
 * faces: failTagged, written by Faces.lean. Do not edit.
 */
import { Effect } from "effect"
import { pair } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<never, readonly ["EmptyTitle", "a title is required"], never> = Effect.fail(
  pair("EmptyTitle", "a title is required")
)
