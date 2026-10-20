/**
 * faces: successCause, written by Faces.lean. Do not edit.
 */
import { type Cause, Effect } from "effect"

export const main: Effect.Effect<Cause.Cause<string>, never, never> = Effect.catchCause(
  Effect.fail("c"),
  (a0) => Effect.succeed(a0)
)
