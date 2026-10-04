import { Option } from "effect"
import { recordOptional, recordSet, recordValue } from "./records.ts"

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
