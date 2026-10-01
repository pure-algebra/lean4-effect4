// Seat T spelling checks (RED CONTROL): each statement must be refused by tsgo 7; the expected code is
// in the comment, and the log is compared against these nine codes.
import { Effect } from "effect"
import type { Brand } from "effect"
import { NotFound, NotFoundOtherTag } from "./idiomatic.js"
type NotFoundP = { readonly _tag: "NotFound"; readonly id: number }
type OptKey = { readonly a?: string }
type ReqUndef = { readonly a: string | undefined }
type T3 = readonly [number, number, number]
declare const nested: readonly [number, readonly [number, number]]
declare const rec: { readonly [k: string]: number }
declare const printedEff: Effect.Effect<number, NotFoundP>
type UserId = string & Brand.Brand<"UserId">
export const r1: NotFound = { _tag: "NotFound", id: 1 } // TS2740: a record literal where the class is expected
export const r2: OptKey = { a: undefined } // TS2375: explicit undefined at an optionalKey field
export const r3: ReqUndef = {} // TS2741: a missing key where the field is required at T | undefined
export const r4: { readonly a: number } = { a: 1, b: 2 } // TS2353: width at a fresh literal
export const r5: T3 = nested // TS2322: nested pairs are not a flat 3-tuple
export const r6: ReadonlyMap<string, number> = rec // TS2740: an index-signature record is not a ReadonlyMap
export const r7: Effect.Effect<number, NotFound> = printedEff // TS2375 (run 1 predicted TS2322; tsgo reports the exactOptionalPropertyTypes variant): a structural error record where the class is expected
export const r8: UserId = "x" // TS2322: a plain string where a branded string is expected
export const r9: NotFound = new NotFoundOtherTag({ id: 1 }) // TS2375 (run 1 predicted TS2322): the same fields under another tag
