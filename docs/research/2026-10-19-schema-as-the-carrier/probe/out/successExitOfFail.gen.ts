/**
 * faces: successExitOfFail, written by Faces.lean. Do not edit.
 */
import { Effect, type Exit } from "effect"

export const main: Effect.Effect<Exit.Exit<never, string>, never, never> = Effect.exit(Effect.fail("inner"))
