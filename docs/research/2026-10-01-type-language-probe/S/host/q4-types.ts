// Seat S, question 4: route U's emitted runtime against the intended types (the same as q3-types.ts
// for route L), checked with tsgo 7. A pass here and a loss in q4-routes.ts's decoders together
// show that the type checker cannot see route U's `__proto__` loss.
import * as U from "./upstream-generated.ts"
type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T
export type RECORD = Assert<Equal<typeof U.RECORD.Type, { readonly a: number; readonly b: string }>>
export type OPTIONAL = Assert<Equal<typeof U.OPTIONAL.Type, { readonly a?: number; readonly b: string }>>
export type MAP = Assert<Equal<typeof U.MAP.Type, { readonly [x: string]: number }>>
export type TAGGED3 = Assert<Equal<typeof U.TAGGED3.Type,
  { readonly _tag: "A"; readonly x: number } | { readonly _tag: "B"; readonly y: string } | { readonly _tag: "C" }>>
export type LIT3 = Assert<Equal<typeof U.LIT3_NESTED.Type, "a" | "b" | "c">>
export type TUPLE3 = Assert<Equal<typeof U.TUPLE3.Type, readonly [number, string, boolean]>>
export type MUTABLE = Assert<Equal<typeof U.MUTABLE.Type, { "a-b"?: string }>>
export type N_PROTO = Assert<Equal<typeof U.N_PROTO.Type, { readonly "__proto__": number }>>
export type SPECIAL = Assert<Equal<typeof U.SPECIAL.Type, {
  readonly "__proto__": number; readonly "a-b": string; readonly "é": boolean; readonly constructor: string;
  readonly "": number; readonly "10": number; readonly "9": number }>>
