// Seat T spelling checks (green): every assertion is what tsgo 7 answers; exit 0 required.
import { Data, Effect, Option, Schema } from "effect"
import type { Brand } from "effect"
import { NotFound as NotFoundIdiomatic, NotFoundOtherTag, UserClass, type Response } from "./idiomatic.js"
type Mutual<A, B> = [A] extends [B] ? ([B] extends [A] ? true : false) : false
type Below<A, B> = [A] extends [B] ? true : false

// A. records
type ResponseP = { readonly body: string; readonly status: number }
export const a1: Mutual<Response, ResponseP> = true
type WindowM = { used: number; admitted: number; rejected: number }
type WindowP = { readonly admitted: number; readonly rejected: number; readonly used: number }
export const a2: Mutual<WindowM, WindowP> = true
export const a3: Mutual<{ readonly a: number; readonly b: string }, { readonly a: number }> = false
export const a4: Mutual<Effect.Effect<Response>, Effect.Effect<ResponseP>> = true
const UserS = Schema.Struct({ id: Schema.Number, name: Schema.String, role: Schema.Literals(["admin", "member"]) })
export const a5: Mutual<typeof UserS.Type, { readonly id: number; readonly name: string; readonly role: "admin" | "member" }> = true

// C. optional keys
type OptKey = { readonly a?: string }
type OptUndef = { readonly a?: string | undefined }
type ReqUndef = { readonly a: string | undefined }
export const c1: Mutual<OptKey, OptUndef> = false
export const c2: Mutual<OptUndef, ReqUndef> = false
export const c3: Mutual<OptKey, ReqUndef> = false
const OK = Schema.Struct({ a: Schema.optionalKey(Schema.String) })
const OU = Schema.Struct({ a: Schema.optional(Schema.String) })
export const c4: Mutual<typeof OK.Type, OptKey> = true
export const c5: Mutual<typeof OU.Type, OptUndef> = true

// D. tagged unions
type Entry = { readonly _tag: "Deposit"; readonly amount: number } | { readonly _tag: "Withdraw"; readonly amount: number }
type EntryP = { readonly _tag: "Withdraw"; readonly amount: number } | { readonly _tag: "Deposit"; readonly amount: number }
export const d1: Mutual<Entry, EntryP> = true
type EntryE = Data.TaggedEnum<{ Deposit: { readonly amount: number }; Withdraw: { readonly amount: number } }>
export const d2: Mutual<Entry, EntryE> = true
const EntryS = Schema.Union([Schema.TaggedStruct("Deposit", { amount: Schema.Number }), Schema.TaggedStruct("Withdraw", { amount: Schema.Number })])
export const d3: Mutual<Entry, typeof EntryS.Type> = true

// E. error payloads
class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
type NotFoundP = { readonly _tag: "NotFound"; readonly id: number }
export const e1: Mutual<NotFound, NotFoundP> = false
export const e2: Below<NotFound, NotFoundP> = true
export const e3: Mutual<Effect.Effect<number, NotFound>, Effect.Effect<number, NotFoundP>> = false
export const e4: Mutual<NotFound, NotFoundIdiomatic> = true
export const e5: Mutual<NotFound, NotFoundOtherTag> = false
class NotFoundS extends Schema.TaggedError<NotFoundS>()("NotFound", { id: Schema.Number }) {}
export const e6: Mutual<NotFound, NotFoundS> = true
export const e7 = Effect.fail(new NotFound({ id: 1 }))
export const e8: Effect.Effect<never, NotFoundIdiomatic> = e7

// F. maps
const M = Schema.Record(Schema.String, Schema.Number)
export const f1: Mutual<typeof M.Type, Readonly<Record<string, number>>> = true
export const f2: Mutual<typeof M.Type, { readonly [k: string]: number }> = true
export const f3: Mutual<typeof M.Type, ReadonlyMap<string, number>> = false

// G. numbers
export const g1: Mutual<typeof Schema.Int.Type, number> = true
export const g2: Mutual<typeof Schema.Number.Type, number> = true

// H. nullable
export const h1: Mutual<string | undefined, Option.Option<string>> = false

// I. Schema.Class
type UserP = { readonly id: number; readonly name: string }
export const i1: Mutual<UserClass, UserP> = true // run 1 expected false: tsgo is structural at Schema.Class
export const i2: Below<UserClass, UserP> = true
export const i3: UserClass = { id: 1, name: "a" }

// J. tuples
type T3 = readonly [number, number, number]
type T3nested = readonly [number, readonly [number, number]]
export const j1: Mutual<T3, T3nested> = false

// K. brands
type UserId = string & Brand.Brand<"UserId">
export const k1: Mutual<UserId, string> = false
export const k2: Below<UserId, string> = true
