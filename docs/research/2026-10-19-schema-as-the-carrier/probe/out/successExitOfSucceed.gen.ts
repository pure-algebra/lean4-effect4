/**
 * faces: successExitOfSucceed, written by Faces.lean. Do not edit.
 */
import { Effect, type Exit } from "effect"

export const main: Effect.Effect<Exit.Exit<number, never>, never, never> = Effect.exit(Effect.succeed(1))
