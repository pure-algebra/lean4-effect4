/**
 * faces: answerIsDeferred, written by Faces.lean. Do not edit.
 */
import { Deferred, type Effect } from "effect"

export const main: Effect.Effect<Deferred.Deferred<number, never>, never, never> = Deferred.make<number, never>()
