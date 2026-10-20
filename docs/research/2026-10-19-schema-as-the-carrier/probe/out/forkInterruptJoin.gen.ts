/**
 * faces: forkInterruptJoin, written by Faces.lean. Do not edit.
 */
import { Effect, Fiber } from "effect"

export const main: Effect.Effect<void, never, never> = Effect.flatMap(
  Effect.forkChild(Effect.sleep(1000), { startImmediately: true, uninterruptible: "inherit" }),
  (a0) => Effect.flatMap(Fiber.interrupt(a0), (a1) => Fiber.join(a0))
)
