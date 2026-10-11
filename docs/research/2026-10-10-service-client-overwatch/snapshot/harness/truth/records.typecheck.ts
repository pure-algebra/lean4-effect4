import { Effect, Option } from "effect"
import { caseTagR, recordRequired, recordOptional, recordSet, recordValue } from "./records.ts"

const person = recordValue<{ readonly id: number; readonly nickname?: string }>([], { id: 1 })
const absent: Option.Option<string> = recordOptional("nickname")(person)
// @ts-expect-error An undeclared field has no reading.
recordOptional("missing")(person)
// @ts-expect-error Present undefined does not inhabit an optional string field.
recordValue<{ readonly nickname?: string }>([], { nickname: undefined })
const present = recordValue<{ readonly nickname?: string | undefined }>([], { nickname: undefined })
const explicit: Option.Option<string | undefined> = recordOptional("nickname")(present)
const updated = recordSet<"nickname">("nickname")(person)(7)
const required: { readonly id: number; readonly nickname: 7 } = updated
const tagged = recordSet<"_tag">("_tag")(person)("Found")
const literal: "Found" = tagged._tag
// @ts-expect-error Required reading refuses an optional declaration.
recordRequired("nickname")(person)
void [absent, explicit, required, literal]


type Search = { readonly _tag: "Found"; readonly id: number } |
  { readonly _tag: "Missing"; readonly query: string } |
  { readonly _tag: "Denied"; readonly reason: string }
const narrowSearch = (value: Search) => caseTagR(value, "Found", hit => {
  const whole: { readonly _tag: "Found"; readonly id: number } = hit
  // @ts-expect-error The hit record has no missing-query field.
  hit.query
  return Effect.succeed(whole.id)
}, miss => {
  const whole: Exclude<Search, { readonly _tag: "Found" }> = miss
  // @ts-expect-error The matching alternative has been removed.
  miss.id
  return Effect.succeed(whole._tag)
})
const allMiss = (value: Search) => caseTagR(value, "Else", hit => {
  const empty: never = hit
  return Effect.succeed(empty)
}, miss => { const whole: Search = miss; return Effect.succeed(whole) })
const allHit = (value: { readonly _tag: "Found"; readonly id: number }) => caseTagR(value,
  "Found", hit => Effect.succeed(hit.id), miss => { const empty: never = miss; return Effect.succeed(empty) })
void [narrowSearch, allMiss, allHit]

const repeatedTag = (value: Search | { readonly _tag: "Found"; readonly name: string }) =>
  caseTagR(value, "Found", hit => {
    const both: { readonly _tag: "Found"; readonly id: number } |
      { readonly _tag: "Found"; readonly name: string } = hit
    // @ts-expect-error Both matching alternatives remain; neither payload is universally present.
    hit.id
    return Effect.succeed(both)
  }, miss => Effect.succeed(miss))
void repeatedTag

// E4-RECORD-CE-013/014/015: impossible branches retain never through every record elimination.
const fixed = { _tag: "Found" as const, id: 7 }
const deadRequired: Effect.Effect<number> = caseTagR(fixed, "Absent", hit =>
  Effect.succeed(recordRequired("id")(hit)), miss => Effect.succeed(miss.id))
const deadOptional: Effect.Effect<number> = caseTagR(fixed, "Absent", hit =>
  Effect.succeed(recordOptional("id")(hit)), miss => Effect.succeed(miss.id))
const deadUpdate: Effect.Effect<number> = caseTagR(fixed, "Absent", hit =>
  Effect.succeed(recordSet("id")(hit)(8)), miss => Effect.succeed(miss.id))
const deadNested: Effect.Effect<number> = caseTagR(fixed, "Absent", hit =>
  Effect.succeed(recordRequired("extra")(recordSet("extra")(recordRequired("child")(hit))(1))),
  miss => Effect.succeed(miss.id))
const oldRequired = (receiver: never) => {
  // @ts-expect-error E4-RECORD-CE-013: the previous dot image fails at never.
  return receiver.id
}
const oldOverwrite = (receiver: never) => {
  // @ts-expect-error E4-RECORD-CE-015: the previous spread image fails at never.
  return { ...receiver, id: 8 }
}
const oldOptional = (receiver: never): Option.Option<never> => {
  void receiver
  return Option.none()
}
// @ts-expect-error E4-RECORD-CE-014: the previous optional result widens the whole program.
const oldOptionalProgram: Effect.Effect<number> = caseTagR(fixed, "Absent", hit =>
  Effect.succeed(oldOptional(hit)), miss => Effect.succeed(miss.id))
void [deadRequired, deadOptional, deadUpdate, deadNested, oldRequired, oldOverwrite, oldOptionalProgram]
