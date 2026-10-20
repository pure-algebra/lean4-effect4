/**
 * faces: interruptNoOne, written by Faces.lean. Do not edit.
 */
import { Cause, Effect } from "effect"

export const main: Effect.Effect<never, never, never> = Effect.failCause(Cause.interrupt())
