/** Retargeted from foldlab experiments/lift-harness/src/contract.ts at 4005d34f.
 * Verdict vocabulary and gate equality. Decoding validates without repairing data.
 * Recognition engines import these types only; their runtime reading logic is independent.
 */
import { Schema } from "effect"
import { Eff } from "../eff.gen.ts"
import { effJson } from "../json.gen.ts"
import { taxonomy } from "../taxonomy.gen.ts"

export const RefusalCode = Schema.Literals(taxonomy.map(row => row.code))
export type RefusalCode = typeof RefusalCode.Type
export const Unit = Schema.Struct({ file: Schema.String, name: Schema.String, span: Schema.Struct({ start: Schema.Number, end: Schema.Number }) })
export const Key = Schema.Struct({ ordinal: Schema.Number, service: Schema.Number, sourceId: Schema.String })
export type Key = typeof Key.Type
export const Lift = Schema.Struct({ kind: Schema.Literal("lifted"), unit: Unit, eff: Eff, keys: Schema.Array(Key), wireHex: Schema.String })
export const Refusal = Schema.Struct({ kind: Schema.Literal("refusal"), unit: Unit, code: RefusalCode, detail: Schema.String, pos: Schema.optional(Schema.Number) })
export const Verdict = Schema.Union([Lift, Refusal])
export type Verdict = typeof Verdict.Type
export const decodeVerdict = Schema.decodeUnknownSync(Verdict)
export const canonJson = (value: unknown): string => {
  if (value === null || typeof value === "boolean" || typeof value === "string") return JSON.stringify(value)
  if (typeof value === "number" && Number.isSafeInteger(value)) return String(value)
  if (Array.isArray(value)) return `[${value.map(canonJson).join(",")}]`
  if (typeof value === "object" && value !== null) return `{${Object.keys(value).sort().map(k => `${JSON.stringify(k)}:${canonJson(Reflect.get(value, k))}`).join(",")}}`
  throw new Error("value outside canonical JSON")
}
export const verdictKey = (v: Verdict): unknown => v.kind === "lifted"
  ? { kind: v.kind, unit: v.unit, eff: effJson(v.eff), keys: v.keys, wireHex: v.wireHex }
  : { kind: v.kind, name: v.unit.name, code: v.code, detail: v.detail }

/** Owner-approved T3 projection: source edits move locations, nothing else is omitted. */
export const sourceEditKey = (v: Verdict): unknown => {
  const { span: _span, ...unit } = v.unit
  if (v.kind === "lifted") return { kind: v.kind, unit, eff: effJson(v.eff), keys: v.keys, wireHex: v.wireHex }
  return { kind: v.kind, unit, code: v.code, detail: v.detail }
}

export const FileReport = Schema.Struct({
  file: Schema.String,
  pins: Schema.String,
  contentDigest: Schema.String,
  ck: Schema.optional(Schema.Array(Verdict)),
  oxc: Schema.optional(Schema.Array(Verdict)),
  ckParsed: Schema.NullOr(Schema.Boolean),
  oxcParsed: Schema.NullOr(Schema.Boolean),
  agreement: Schema.Literals(["agree", "disagree", "single"])
})
export type FileReport = typeof FileReport.Type
export const decodeFileReport = Schema.decodeUnknownSync(FileReport)

export const encodeReport = (r: FileReport): unknown => ({ ...r,
  ...(r.ck ? { ck: r.ck.map(v => v.kind === "lifted" ? { ...v, eff: effJson(v.eff) } : v) } : {}),
  ...(r.oxc ? { oxc: r.oxc.map(v => v.kind === "lifted" ? { ...v, eff: effJson(v.eff) } : v) } : {})
})
