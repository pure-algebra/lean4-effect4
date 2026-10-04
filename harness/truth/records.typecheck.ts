import { Effect, Option } from "effect"
import { caseTagR, recordOptional, recordSet, recordValue } from "./records.ts"

const person = recordValue<{ readonly id: number; readonly nickname?: string }>([], { id: 1 })
const absent: Option.Option<string> = recordOptional("nickname")(person)
// @ts-expect-error An undeclared field has no reading.
recordOptional("missing")(person)
// @ts-expect-error Present undefined does not inhabit an optional string field.
recordValue<{ readonly nickname?: string }>([], { nickname: undefined })
const present = recordValue<{ readonly nickname?: string | undefined }>([], { nickname: undefined })
const explicit: Option.Option<string | undefined> = recordOptional("nickname")(present)
const updated = recordSet<"nickname">()({ ...person, nickname: 7 })
const required: { readonly id: number; readonly nickname: 7 } = updated
const tagged = recordSet<"_tag">()({ ...person, _tag: "Found" })
const literal: "Found" = tagged._tag
// @ts-expect-error The update requires its named field.
recordSet<"nickname">()({ id: 1 })
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
