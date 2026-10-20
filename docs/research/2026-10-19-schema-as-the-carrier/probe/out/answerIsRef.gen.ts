/**
 * faces: answerIsRef, written by Faces.lean. Do not edit.
 */
import { type Effect, Ref } from "effect"

export const main: Effect.Effect<Ref.Ref<number>, never, never> = Ref.make(1)
