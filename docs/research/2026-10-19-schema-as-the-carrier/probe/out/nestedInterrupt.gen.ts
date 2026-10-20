/**
 * faces: nestedInterrupt, written by Faces.lean. Do not edit.
 */
import { Effect, type Exit, Fiber } from "effect"

export const main: Effect.Effect<Exit.Exit<void, never>, never, never> = Effect.flatMap(
  Effect.forkChild(Effect.sleep(1000), { startImmediately: true, uninterruptible: "inherit" }),
  (a0) => Effect.flatMap(Fiber.interrupt(a0), (a1) => Effect.exit(Fiber.join(a0)))
)
