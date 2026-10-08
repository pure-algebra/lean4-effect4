import { Option } from "effect"
import { recordOptional } from "./records.ts"

// These inspect the actual helper signature. They are separate from Lean-emitted fixtures.
export const singleRecordUnionPayload = (value: { readonly x: number | string }) => recordOptional("x")(value)
export const optionalRecordUnion = (value: { readonly x?: number; readonly left: boolean } |
  { readonly x?: string; readonly right: boolean }) => recordOptional("x")(value)
export const neverReceiver = (value: never) => recordOptional("x")(value)
export const ownUndefinedType = (value: { readonly x?: undefined }) => recordOptional("x")(value)

const missingProperty: { readonly x?: undefined } = {}
const ownUndefined: { readonly x?: undefined } = { x: undefined }
const inheritedProperty = Object.create({ x: undefined }) as { readonly x?: undefined }
const absent = recordOptional("x")(missingProperty)
const present = recordOptional("x")(ownUndefined)
const inherited = recordOptional("x")(inheritedProperty)
if (!Option.isNone(absent)) throw new Error("missing property must return None")
if (!Option.isSome(present) || present.value !== undefined) throw new Error("own undefined must return Some(undefined)")
if (!Option.isNone(inherited)) throw new Error("inherited property must return None")
console.log(JSON.stringify({ missingProperty: "None", ownUndefined: "Some(undefined)", inheritedProperty: "None" }))
