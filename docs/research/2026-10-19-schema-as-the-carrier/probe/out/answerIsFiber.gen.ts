/**
 * faces: answerIsFiber, written by Faces.lean. Do not edit.
 */
import { Effect, type Fiber } from "effect"

export const main: Effect.Effect<Fiber.Fiber<void, never>, never, never> = Effect.forkChild(
  Effect.succeed(undefined),
  { startImmediately: true, uninterruptible: "inherit" }
)
