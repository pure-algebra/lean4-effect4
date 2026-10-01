// Seat T: does a tagged error class's NAME matter to tsgo, or only its tag and fields? (green: exit 0)
import { Data, Effect, Schema } from "effect"
type Mutual<A, B> = [A] extends [B] ? ([B] extends [A] ? true : false) : false
class NotFoundError extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
class NotFoundS extends Schema.TaggedError<NotFoundS>()("NotFound", { id: Schema.Number }) {}
class NotFoundSError extends Schema.TaggedError<NotFoundSError>()("NotFound", { id: Schema.Number }) {}
class Wider extends Data.TaggedError("NotFound")<{ readonly id: number; readonly url: string }> {}
export const n1: Mutual<NotFoundError, NotFound> = true // the class name does not matter
export const n2: Mutual<NotFoundS, NotFoundSError> = true // nor for the Schema form
export const n3: Mutual<NotFoundError, NotFoundS> = true // nor across the Data and Schema forms
export const n4: Mutual<NotFound, Wider> = false // the fields do
export const n5: Mutual<Effect.Effect<1, NotFoundError | Wider>, Effect.Effect<1, NotFound | Wider>> = true
export const n6: NotFoundError = new NotFound({ id: 1 }) // a value of one class where the other is expected
