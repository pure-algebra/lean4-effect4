/**
 * faces: successSome, written by Faces.lean. Do not edit.
 */
import { Effect, type Option } from "effect"
import { some } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<Option.Option<number>, never, never> = Effect.succeed(some(3))
