/** RED CONTROL (must fail): the GREEN file's expected errors with the directives removed. */
import { Data, Schema } from "effect"
type A = { readonly id: number; readonly name: string }
export const w2: A = { id: 1, name: "a", extra: true }
declare const opt: { readonly a?: string }
export const o2: { readonly a: string } = opt
declare const undef: { readonly a: undefined }
export const o3: { readonly a?: string } = undef
const K = Schema.Struct({ a: Schema.optionalKey(Schema.String) })
export const s3: typeof K.Type = undef
class NotFound extends Schema.TaggedError<NotFound>()("NotFound", { id: Schema.Number }) {}
export const e1: NotFound = { _tag: "NotFound", id: 1 }
class HttpError extends Data.TaggedError("HttpError")<{ readonly status: number }> {}
export const e3: HttpError = { _tag: "HttpError", status: 1 }
class Gone extends Data.TaggedError("Gone")<{ readonly status: number }> {}
export const e4: HttpError = new Gone({ status: 1 })
