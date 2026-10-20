/**
 * faces: failRecord, written by Faces.lean. Do not edit.
 */
import { Data, Effect } from "effect"

export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}

export const main: Effect.Effect<never, NotFound, never> = Effect.fail(new NotFound({ id: 7 }))
