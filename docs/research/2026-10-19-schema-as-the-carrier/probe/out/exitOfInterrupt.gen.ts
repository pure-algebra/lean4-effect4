/**
 * faces: exitOfInterrupt, written by Faces.lean. Do not edit.
 */
import { Cause, Effect, type Exit } from "effect"

export const main: Effect.Effect<Exit.Exit<never, never>, never, never> = Effect.exit(
  Effect.failCause(Cause.interrupt())
)
