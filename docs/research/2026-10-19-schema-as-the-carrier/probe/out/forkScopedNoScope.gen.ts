/**
 * faces: forkScopedNoScope, written by Faces.lean. Do not edit.
 */
import { Effect, type Fiber, type Scope } from "effect"

export const main: Effect.Effect<Fiber.Fiber<void, never>, never, Scope.Scope> = Effect.forkScoped(
  Effect.succeed(undefined),
  { startImmediately: false, uninterruptible: "inherit" }
)
