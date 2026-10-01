// Seat R, question 3: each printed type form against the type rc.112's Schema gives the same
// data (B-print asks for mutual assignability). `Same<A, B>` is checked both ways by assignment.
import { Option, Schema } from "effect"

declare const mutual: <A, B>(a: [A] extends [B] ? ([B] extends [A] ? true : false) : false) => void

// records: readonly fields, canonical order by name (any order is the same type)
const User = Schema.Struct({ id: Schema.Number, name: Schema.String, role: Schema.Literals(["admin", "member"]) })
type UserPrinted = { readonly id: number; readonly name: string; readonly role: "admin" | "member" }
mutual<UserPrinted, typeof User.Type>(true)
type UserPermuted = { readonly role: "admin" | "member"; readonly name: string; readonly id: number }
mutual<UserPrinted, UserPermuted>(true)
// non-identifier names quoted
const Header = Schema.Struct({ "content-type": Schema.String, default: Schema.Boolean })
mutual<{ readonly "content-type": string; readonly default: boolean }, typeof Header.Type>(true)

// optional keys (stage 4): optionalKey is `a?: τ`; optional is `a?: τ | undefined`
const OK = Schema.Struct({ a: Schema.optionalKey(Schema.Number) })
const OP = Schema.Struct({ a: Schema.optional(Schema.Number) })
mutual<{ readonly a?: number }, typeof OK.Type>(true)
mutual<{ readonly a?: number | undefined }, typeof OP.Type>(true)

// keyed maps: Schema.Record is an index-signature object; Schema.ReadonlyMap a Map
const RecordSchema = Schema.Record(Schema.String, Schema.Number)
mutual<Readonly<Record<string, number>>, typeof RecordSchema.Type>(true)
mutual<{ readonly [x: string]: number }, typeof RecordSchema.Type>(true)
const MapSchema = Schema.ReadonlyMap(Schema.String, Schema.Number)
mutual<ReadonlyMap<string, number>, typeof MapSchema.Type>(true)

// tagged unions: a union of records with a literal `_tag`
const Entry = Schema.Union([
  Schema.TaggedStruct("Deposit", { amount: Schema.Number }),
  Schema.TaggedStruct("Withdraw", { amount: Schema.Number })
])
type EntryPrinted =
  | { readonly _tag: "Deposit"; readonly amount: number }
  | { readonly _tag: "Withdraw"; readonly amount: number }
mutual<EntryPrinted, typeof Entry.Type>(true)

// the tag select on records, printed through a prelude helper that narrows by `_tag`
export const caseTagR = <S extends { readonly _tag: string }, T extends S["_tag"], A, B>(
  s: S, tag: T, hit: (s: Extract<S, { readonly _tag: T }>) => A, miss: (s: Exclude<S, { readonly _tag: T }>) => B
): A | B => (s._tag === tag ? hit(s as Extract<S, { readonly _tag: T }>) : miss(s as Exclude<S, { readonly _tag: T }>))
declare const e: EntryPrinted
export const amount: number = caseTagR(e, "Deposit", (d) => d.amount, (w) => -w.amount)
export const narrowed: "Withdraw" = caseTagR(e, "Deposit", () => "Withdraw" as const, (w) => w._tag)
// an option of a record prints through Option
export const someUser: Option.Option<UserPrinted> = Option.some({ id: 1, name: "ada", role: "admin" })
