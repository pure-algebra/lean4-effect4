// Seat S, question 2 (types half): the exact inferred `Type` of each per-form spelling, checked
// with tsgo 7 against the installed rc.112 declarations. `Assert<Equal<…>>` fails with TS2344 when
// the inferred type differs; every `@ts-expect-error` is a rejecting control (TS2578 if unused).
import * as Schema from "effect/Schema"

type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T

// records, permuted: one type whatever the written order
export const AB = Schema.Struct({ a: Schema.Number, b: Schema.String })
export const BA = Schema.Struct({ b: Schema.String, a: Schema.Number })
export type T1 = Assert<Equal<typeof AB.Type, { readonly a: number; readonly b: string }>>
export type T2 = Assert<Equal<typeof BA.Type, typeof AB.Type>>
// @ts-expect-error a missing field
export const ab1: typeof AB.Type = { a: 1 }
// @ts-expect-error a wrong field type
export const ab2: typeof AB.Type = { a: "1", b: "x" }
// @ts-expect-error an excess property in a fresh literal
export const ab3: typeof AB.Type = { a: 1, b: "x", c: true }
export const ab4: typeof AB.Type = { b: "x", a: 1 } // a permuted literal is accepted
declare const abv: typeof AB.Type
// @ts-expect-error readonly
abv.a = 2

// optional keys: optionalKey versus optional under exactOptionalPropertyTypes
export const OK = Schema.Struct({ a: Schema.optionalKey(Schema.Number) })
export const OP = Schema.Struct({ a: Schema.optional(Schema.Number) })
export type T3 = Assert<Equal<typeof OK.Type, { readonly a?: number }>>
export type T4 = Assert<Equal<typeof OP.Type, { readonly a?: number | undefined }>>
// @ts-expect-error optionalKey refuses an explicit undefined
export const ok1: typeof OK.Type = { a: undefined }
export const op1: typeof OP.Type = { a: undefined }
export const ok2: typeof OK.Type = {}

// mutableKey drops readonly; with optionalKey both modifiers show
export const MK = Schema.Struct({ a: Schema.mutableKey(Schema.Number) })
export type T5 = Assert<Equal<typeof MK.Type, { a: number }>>
export const MOK = Schema.Struct({ "a-b": Schema.optionalKey(Schema.mutableKey(Schema.String)) })
export type T6 = Assert<Equal<typeof MOK.Type, { "a-b"?: string }>>

// maps
export const RN = Schema.Record(Schema.String, Schema.Number)
export type T7 = Assert<Equal<typeof RN.Type, { readonly [x: string]: number }>>
// @ts-expect-error a wrong value type
export const rn1: typeof RN.Type = { a: "x" }

// tagged unions
export const A = Schema.TaggedStruct("A", { x: Schema.Number })
export const B = Schema.TaggedStruct("B", { y: Schema.String })
export const AorB = Schema.Union([A, B])
export type T8 = Assert<Equal<typeof AorB.Type,
  { readonly _tag: "A"; readonly x: number } | { readonly _tag: "B"; readonly y: string }>>
// @ts-expect-error the payload of the other case
export const u1: typeof AorB.Type = { _tag: "A", y: "s" }

// tuples are not arrays; literal unions
export const T1S = Schema.Tuple([Schema.String])
export const ARR = Schema.Array(Schema.String)
export type T9 = Assert<Equal<typeof T1S.Type, readonly [string]>>
export type T10 = Assert<Equal<typeof ARR.Type, ReadonlyArray<string>>>
// @ts-expect-error a tuple needs its element
export const t1: typeof T1S.Type = []
export const LIT = Schema.Literals(["a", "b", "c"])
export type T11 = Assert<Equal<typeof LIT.Type, "a" | "b" | "c">>

// numbers with the checks Bridge.schema writes: the type is number; the checks are run-time only
export const NAT = Schema.Number.check(Schema.isInt(), Schema.isGreaterThanOrEqualTo(0))
export const INT = Schema.Number.check(Schema.isInt())
export type T12 = Assert<Equal<typeof NAT.Type, number>>
export type T13 = Assert<Equal<typeof INT.Type, number>>
export type T14 = Assert<Equal<typeof Schema.Natural.Type, number>>

// property spelling: computed, quoted, Object.fromEntries; Unicode; constructor; empty
export const COMPUTED = Schema.Struct({ ["__proto__"]: Schema.Number, ["a-b"]: Schema.String })
export type T15 = Assert<Equal<typeof COMPUTED.Type, { readonly "__proto__": number; readonly "a-b": string }>>
export const QUOTED = Schema.Struct({ "a-b": Schema.String, "é": Schema.Number, "日本": Schema.Boolean })
export type T16 = Assert<Equal<typeof QUOTED.Type, { readonly "a-b": string; readonly "é": number; readonly "日本": boolean }>>
export const IDENT = Schema.Struct({ é: Schema.Number, constructor: Schema.String, toString: Schema.String })
export type T17 = Assert<Equal<typeof IDENT.Type, { readonly é: number; readonly constructor: string; readonly toString: string }>>
export const EMPTY = Schema.Struct({ "": Schema.Number })
export type T18 = Assert<Equal<typeof EMPTY.Type, { readonly "": number }>>
export const ENTRIES = Schema.Struct(Object.fromEntries([["a-b", Schema.String]]))
// the entries spelling loses the field list: an empty object type-checks against it
export const entries1: typeof ENTRIES.Type = {}
