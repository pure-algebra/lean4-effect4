/**
 * faces: forkDieJoin, written by Faces.lean. Do not edit.
 */
import { Cause, Effect, Fiber } from "effect"

export const main: Effect.Effect<never, never, never> = Effect.flatMap(
  Effect.forkChild(Effect.failCause(Cause.die(9)), { startImmediately: true, uninterruptible: "inherit" }),
  (a0) => Fiber.join(a0)
)
