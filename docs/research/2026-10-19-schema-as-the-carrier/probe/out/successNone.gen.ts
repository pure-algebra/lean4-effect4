/**
 * faces: successNone, written by Faces.lean. Do not edit.
 */
import { Effect, type Option } from "effect"
import { none } from "../../../../../harness/truth/prelude.ts"

export const main: Effect.Effect<Option.Option<never>, never, never> = Effect.succeed(none())
