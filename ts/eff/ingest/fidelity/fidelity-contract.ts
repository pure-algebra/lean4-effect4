import { Schema } from "effect"
import { Key, Unit } from "../contract.ts"
import { Generation } from "../census/census-contract.ts"
export const InputVerdict = Schema.Union([
  Schema.Struct({ kind: Schema.Literal("lifted"), unit: Unit, wireHex: Schema.String, keys: Schema.Array(Key) }),
  Schema.Struct({ kind: Schema.Literal("refusal"), unit: Unit })
])
export const InputFile = Schema.Struct({ project: Schema.String, file: Schema.String, generation: Schema.NullOr(Generation), pins: Schema.String, contentDigest: Schema.String, ck: Schema.optional(Schema.Array(InputVerdict)), oxc: Schema.optional(Schema.Array(InputVerdict)) })
export type InputFile = typeof InputFile.Type
export const decodeInput = Schema.decodeUnknownSync(InputFile)
export const Printed = Schema.Struct({ wireHex: Schema.String, wellTyped: Schema.Boolean, requiresEmpty: Schema.NullOr(Schema.Boolean), decl: Schema.NullOr(Schema.String) })
export type Printed = typeof Printed.Type
export const decodePrinted = Schema.decodeUnknownSync(Printed)
export const Observation = Schema.Struct({ exit: Schema.Unknown, parked: Schema.Boolean, schedule: Schema.Array(Schema.String) })
export const Observed = Schema.Union([
  Schema.Struct({ status: Schema.Literal("observed"), effect: Schema.Literal("4.0.0-rc.112"), timeoutMs: Schema.Number, observation: Observation }),
  Schema.Struct({ status: Schema.Literal("could-not-run"), error: Schema.String })
])
export type Observed = typeof Observed.Type
export const decodeObserved = Schema.decodeUnknownSync(Observed)
export interface Candidate { file: InputFile; name: string; occurrence: number; span: { readonly start: number; readonly end: number }; variants: { wireHex: string; keys: readonly (typeof Key.Type)[]; engines: string[] }[] }
