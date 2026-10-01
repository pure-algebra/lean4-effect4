/**
 * Seat EFFECT, data probe (2026-10-01): what assignability means at object types, checked by the
 * pinned tsgo with the flags the pass used (strict, exactOptionalPropertyTypes). GREEN: must
 * compile; every line marked `@ts-expect-error` must be an error, or tsgo reports TS2578.
 */
import { Data, Effect, Schema } from "effect"

type A = { readonly id: number; readonly name: string }
type Wide = { readonly id: number; readonly name: string; readonly extra: boolean }

declare const wide: Wide
// width: a value with more properties is assignable to a type with fewer
export const w1: A = wide
// a fresh object literal with an unknown property is refused (excess-property check, TS2353)
// @ts-expect-error
export const w2: A = { id: 1, name: "a", extra: true }

// depth: readonly properties are covariant
declare const narrow: { readonly tag: "x"; readonly n: 1 }
export const d1: { readonly tag: string; readonly n: number } = narrow

// optionality: required into optional is fine, optional into required is refused
declare const req: { readonly a: string }
declare const opt: { readonly a?: string }
export const o1: { readonly a?: string } = req
// @ts-expect-error
export const o2: { readonly a: string } = opt
// exactOptionalPropertyTypes: an optional key does not admit an explicit undefined
declare const undef: { readonly a: undefined }
// @ts-expect-error
export const o3: { readonly a?: string } = undef
// ... unless the type says so, as Schema.optional does
export const o4: { readonly a?: string | undefined } = undef

// Schema.Struct's Type is the object type literal, in both directions
const User = Schema.Struct({ id: Schema.Number, name: Schema.String })
type U = typeof User.Type
declare const u: U
declare const a: A
export const s1: A = u
export const s2: U = a
// Schema.optionalKey and Schema.optional give the two optional spellings above
const K = Schema.Struct({ a: Schema.optionalKey(Schema.String) })
const O = Schema.Struct({ a: Schema.optional(Schema.String) })
// @ts-expect-error
export const s3: typeof K.Type = undef
export const s4: typeof O.Type = undef

// a tagged error is a class: an object literal with its fields is not one
class NotFound extends Schema.TaggedError<NotFound>()("NotFound", { id: Schema.Number }) {}
// @ts-expect-error
export const e1: NotFound = { _tag: "NotFound", id: 1 }
export const e2: NotFound = new NotFound({ id: 1 })
// ... and a class instance is accepted at its fields' object type
export const e5: { readonly _tag: "NotFound"; readonly id: number } = new NotFound({ id: 1 })
class HttpError extends Data.TaggedError("HttpError")<{ readonly status: number }> {}
// @ts-expect-error
export const e3: HttpError = { _tag: "HttpError", status: 1 }
// two tagged errors with the same fields and different tags are distinct by `_tag`
class Gone extends Data.TaggedError("Gone")<{ readonly status: number }> {}
// @ts-expect-error
export const e4: HttpError = new Gone({ status: 1 })
// the error channel of a failing program is the class, and SchemaError joins it from a decode
export const p1: Effect.Effect<never, NotFound> = Effect.fail(new NotFound({ id: 1 }))
export const p2: Effect.Effect<U, Schema.SchemaError> = Schema.decodeUnknownEffect(User)({})

// TypeScript accepts an optional target key the source does not declare, so membership is not
// monotone at this rule: `hole.x` is a number at run time (rc112-schema-behaviour.ts T19)
declare const hasX: { readonly x: number; readonly y: number }
const onlyY: { readonly y: number } = hasX
export const hole: { readonly x?: string; readonly y: number } = onlyY
