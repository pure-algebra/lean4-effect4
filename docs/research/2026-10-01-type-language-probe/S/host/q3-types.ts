// Seat S, question 3: the exact inferred `Type` of each readable emission (generated-profile.ts,
// written by q3-profile.ts from Lean's text), checked with tsgo 7. TS2344 on any difference.
import * as G from "./generated-profile.ts"
type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T
export type NAT = Assert<Equal<typeof G.NAT.Type, number>>
export type INT = Assert<Equal<typeof G.INT.Type, number>>
export type RECORD = Assert<Equal<typeof G.RECORD.Type, { readonly a: number; readonly b: string }>>
export type OPTIONAL = Assert<Equal<typeof G.OPTIONAL.Type, { readonly a?: number; readonly b: string }>>
export type OPTIONAL_UNDEF = Assert<Equal<typeof G.OPTIONAL_UNDEF.Type, { readonly a?: number | undefined }>>
export type MAP = Assert<Equal<typeof G.MAP.Type, { readonly [x: string]: number }>>
export type TAGGED2 = Assert<Equal<typeof G.TAGGED2.Type,
  { readonly _tag: "A"; readonly x: number } | { readonly _tag: "B"; readonly y: string }>>
export type TAGGED3 = Assert<Equal<typeof G.TAGGED3.Type,
  { readonly _tag: "A"; readonly x: number } | { readonly _tag: "B"; readonly y: string } | { readonly _tag: "C" }>>
export type LIT3 = Assert<Equal<typeof G.LIT3_NESTED.Type, "a" | "b" | "c">>
export type LIT3F = Assert<Equal<typeof G.LIT3_FLAT.Type, "a" | "b" | "c">>
export type TUPLE3 = Assert<Equal<typeof G.TUPLE3.Type, readonly [number, string, boolean]>>
export type ARRAY = Assert<Equal<typeof G.ARRAY.Type, ReadonlyArray<string>>>
export type NESTED = Assert<Equal<typeof G.NESTED.Type, { readonly user: { readonly age: number; readonly name: string } }>>
export type SPECIAL = Assert<Equal<typeof G.SPECIAL.Type, {
  readonly "__proto__": number; readonly "a-b": string; readonly "é": boolean; readonly constructor: string;
  readonly "": number; readonly "10": number; readonly "9": number }>>
export type ESCAPED = Assert<Equal<typeof G.ESCAPED.Type, { readonly 'x"y': string; readonly a: number }>>
export type MUTABLE = Assert<Equal<typeof G.MUTABLE.Type, { "a-b"?: string }>>
// rejecting controls
// @ts-expect-error a missing field
export const r1: typeof G.RECORD.Type = { a: 1 }
// @ts-expect-error a wrong case payload
export const r2: typeof G.TAGGED2.Type = { _tag: "A", y: "s" }
// @ts-expect-error a tuple needs its arity
export const r3: typeof G.TUPLE3.Type = [1, "x"]
// @ts-expect-error optionalKey refuses an explicit undefined
export const r4: typeof G.OPTIONAL.Type = { a: undefined, b: "x" }
// @ts-expect-error a map's value type
export const r5: typeof G.MAP.Type = { a: "x" }
// @ts-expect-error the computed __proto__ is a required own field
export const r6: typeof G.SPECIAL.Type = { "a-b": "x", "é": true, constructor: "c", "": 1, "10": 2, "9": 3 }
declare const rec: typeof G.RECORD.Type
// @ts-expect-error readonly
rec.a = 2
