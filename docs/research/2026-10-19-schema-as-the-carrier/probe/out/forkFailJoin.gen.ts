/**
 * faces: forkFailJoin, written by Faces.lean. Do not edit.
 */
import { Effect, Fiber } from "effect"

export const main: Effect.Effect<never, string, never> = Effect.flatMap(
  Effect.forkChild(Effect.fail("child"), { startImmediately: true, uninterruptible: "inherit" }),
  (a0) => Fiber.join(a0)
)
