/** The census probe: each Schema construct of rc.112, what its persisted document keeps, whether
 * revival restores its meaning, and whether rc.112 writes code for it.
 *
 * Run in `ts/eff`: `bun probe/schema-interop/census.run.ts`. Each row is one observation of the
 * pinned host. A row states its expectation, and a failed expectation throws. Samples come from
 * the vessel dogfood's domain (`Test/Dogfood/Scenario/Vessel/Domain.lean` on branch
 * `codex/vessel-dogfood`). */
import { Effect, Option, Schema, SchemaAST, SchemaIssue, SchemaRepresentation, SchemaTransformation } from "effect"
import { isDeepStrictEqual } from "node:util"

type Json = Schema.Json
const firstLine = (e: unknown) => String(e instanceof Error ? e.message : e).split("\n").slice(0, 2).join(" ").slice(0, 140)
type Top = Schema.Top
type Codec = Schema.Codec<unknown, unknown>

/** Every reviver rc.112 exports (75 at the pin, each with an id): each `Schema.*Reviver`. */
export const builtins: ReadonlyArray<SchemaRepresentation.AnyReviver> = Object.entries(Schema)
  .filter(([name]) => name.endsWith("Reviver"))
  .map(([, reviver]) => reviver as SchemaRepresentation.AnyReviver)

// `N_S` (`Schema/Bridge.lean` `normAnn`, `erasedKeys`), as the named-types probe copies it.
const erasedKeys = ["identifier", "title", "description", "documentation", "examples", "default", "message",
  "expected", "arbitrary", "~identifier"]
export const normS = (value: unknown): unknown => {
  if (Array.isArray(value)) return value.map(normS)
  if (value === null || typeof value !== "object") return value
  const out: Record<string, unknown> = {}
  for (const [key, inner] of Object.entries(value)) {
    if (key === "annotations" && inner !== null && typeof inner === "object") {
      const kept = Object.entries(inner).filter(([k]) => !erasedKeys.includes(k))
      if (kept.length > 0) out[key] = Object.fromEntries(kept)
    } else out[key] = normS(inner)
  }
  return out
}

/** The document rc.112 writes for a Schema (`toRepresentation`, its encoded side), through its
 * JSON codec (`toJson`), modulo `N_S`; or why the codec refuses it. */
export const docOf = (schema: Top): { readonly json: Json } | { readonly error: string } => {
  try { return { json: normS(SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(schema.ast))) as Json } }
  catch (e) { return { error: firstLine(e) } }
}
export const doc = (schema: Top): Json => {
  const d = docOf(schema)
  if ("error" in d) throw new Error(d.error)
  return d.json
}
/** The document of the type side (`SchemaAST.toType` first), or why the codec refuses it. */
export const typeDocOf = (schema: Top): { readonly json: Json } | { readonly error: string } => {
  try { return { json: normS(SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(SchemaAST.toType(schema.ast)))) as Json } }
  catch (e) { return { error: firstLine(e) } }
}
/** JSON text that shows `NaN` and `-0`, which `JSON.stringify` writes as `null` and `0`. */
export const show = (value: unknown): string => JSON.stringify(value, (_k, v) =>
  typeof v === "number" && (Number.isNaN(v) || Object.is(v, -0)) ? `<${Object.is(v, -0) ? "-0" : "NaN"}>` : v)

type Revived = { readonly ok: true; readonly schema: Top } | { readonly ok: false; readonly error: string }
export const revive = (json: Json, extra: ReadonlyArray<SchemaRepresentation.AnyReviver> = []): Revived => {
  try {
    return { ok: true, schema: SchemaRepresentation.fromRepresentation(SchemaRepresentation.fromJson(json),
      { revivers: [...builtins, ...extra] }) }
  } catch (e) { return { ok: false, error: firstLine(e) } }
}
/** rc.112's code of a Schema, from its own representation (`toCodeDocument`). */
export const code = (schema: Top): string => {
  try {
    const c = SchemaRepresentation.toCodeDocument(SchemaRepresentation.toMultiDocument(
      SchemaRepresentation.toRepresentation(schema.ast)))
    const refs = [...c.references.nonRecursives.map(r => `${r.$ref} = ${r.code.runtime}`),
      ...Object.entries(c.references.recursives).map(([k, r]) => `${k} = ${r.runtime}`)]
    return [...refs, c.codes[0]!.runtime].join("; ")
  } catch (e) { return `throws ${firstLine(e)}` }
}

/** A decode's outcome: the value, or each issue's path and message. */
export type Outcome = { readonly ok: unknown } | { readonly issues: ReadonlyArray<{ readonly path: string; readonly message: string }> }
const format = SchemaIssue.makeFormatterStandardSchemaV1()
export const decode = (schema: Top, input: unknown): Outcome => {
  const r = Schema.decodeUnknownExit(schema as Codec)(input)
  if (r._tag === "Success") return { ok: r.value }
  const err = (r.cause as unknown as { reasons: ReadonlyArray<{ error?: { issue?: SchemaIssue.Issue } }> }).reasons[0]?.error?.issue
  if (err === undefined) return { issues: [{ path: "", message: "a defect" }] }
  return { issues: format(err).issues.map(i => ({ path: (i.path ?? []).map(String).join("."), message: i.message.slice(0, 80) })) }
}
export const encode = (schema: Top, value: unknown): Outcome => {
  const r = Schema.encodeUnknownExit(schema as Codec)(value)
  if (r._tag === "Success") return { ok: r.value }
  const err = (r.cause as unknown as { reasons: ReadonlyArray<{ error?: { issue?: SchemaIssue.Issue } }> }).reasons[0]?.error?.issue
  if (err === undefined) return { issues: [{ path: "", message: "a defect" }] }
  try { return { issues: format(err).issues.map(i => ({ path: (i.path ?? []).map(String).join("."), message: i.message.slice(0, 80) })) } }
  catch { return { issues: [{ path: "", message: `an issue rc.112's formatter cannot print (${err._tag})` }] } }
}
const okOf = (o: Outcome) => "ok" in o
const sameOutcome = (a: Outcome, b: Outcome) => okOf(a) === okOf(b) && (!okOf(a) || isDeepStrictEqual(a, b))

/** One census row. `samples` are encoded inputs. `expect` is the behaviour the row asserts. */
interface Row {
  readonly id: string
  readonly construct: string
  readonly schema: Top
  readonly samples: ReadonlyArray<unknown>
  readonly extra?: ReadonlyArray<SchemaRepresentation.AnyReviver>
  readonly expect: {
    /** rc.112's document JSON codec writes the document. */
    readonly writes: boolean
    /** The document holds the construct (a check's id, a brand, an optional key, a declaration). */
    readonly kept: boolean
    /** rc.112 revives the document. */
    readonly revives: boolean
    /** The revived Schema decodes every sample as the original does. */
    readonly sameDecoding: boolean
    /** rc.112 writes code for the revived Schema (or for the original, when revival fails). */
    readonly code: boolean
  }
  /** What in the document carries the construct: a predicate over the document's text. */
  readonly keptBy: (text: string) => boolean
}

let observations = 0
let failures = 0
const say = (line: string) => { observations++; console.log(line) }
export const runRows = (rows: ReadonlyArray<Row>) => {
  for (const row of rows) {
    const written = docOf(row.schema)
    const text = "json" in written ? JSON.stringify(written.json) : `refused: ${written.error}`
    const kept = "json" in written && row.keptBy(text)
    const revived: Revived = "json" in written ? revive(written.json, row.extra) : { ok: false, error: "no document" }
    const sameDecoding = revived.ok && row.samples.every(s => sameOutcome(decode(row.schema, s), decode(revived.schema, s)))
    const codeText = code(revived.ok ? revived.schema : row.schema)
    const hasCode = !codeText.startsWith("throws")
    const got = { writes: "json" in written, kept, revives: revived.ok, sameDecoding, code: hasCode }
    const ok = isDeepStrictEqual(got, row.expect)
    if (!ok) failures++
    say(`${ok ? "ok  " : "FAIL"} ${row.id} ${row.construct}: writes ${"json" in written}, kept ${kept}, revives ${revived.ok ? "yes" : `no (${revived.error})`}, ` +
      `same decoding ${sameDecoding}, code ${hasCode ? "yes" : "no"}`)
    say(`       document ${text.length > 300 ? text.slice(0, 300) + "…" : text}`)
    say(`       code ${codeText.length > 300 ? codeText.slice(0, 300) + "…" : codeText}`)
    for (const s of row.samples) {
      const a = decode(row.schema, s)
      const b = revived.ok ? decode(revived.schema, s) : undefined
      say(`       sample ${JSON.stringify(s)}: original ${JSON.stringify(a)}${b === undefined ? "" : `, revived ${JSON.stringify(b)}`}`)
    }
  }
}
export const finish = (name: string) => {
  if (failures > 0) throw new Error(`${failures} row(s) disagree with rc.112`)
  console.log(`PASS schema-interop ${name}: ${observations} observations`)
}

// ---- the vessel domain's samples ------------------------------------------------------------

/** `Positive` (Domain.lean): a natural above zero. Lean's natural is `[isInt, ≥ 0]` (`Bridge.schemaAlg`). */
const Nat = Schema.Number.check(Schema.isInt(), Schema.isGreaterThanOrEqualTo(0))
const Positive = Schema.Number.check(Schema.isInt(), Schema.isGreaterThan(0))
const FlowRate = Positive.pipe(Schema.brand("FlowRate"))
const Unit = Schema.Literals(["microlitrePerSecond", "second", "millimetre", "microlitre",
  "litrePerMinute", "minute", "metre", "cubicMetre"])
const LevelDatum = Schema.Literals(["internalBottom", "siteElevation"])
const DesignRef = Schema.Struct({
  vesselId: Schema.String.check(Schema.isNonEmpty()),
  revision: Schema.Number.check(Schema.isInt(), Schema.isBetween({ minimum: 1, maximum: 1000000000 }))
})
const evidenceKinds = ["geometry", "levelSimulation", "stepAssembly"] as const
const Evidence = Schema.TaggedUnion({
  geometry: { tool: Schema.String, artifactId: Schema.String, passed: Schema.Boolean },
  levelSimulation: { tool: Schema.String, artifactId: Schema.String, passed: Schema.Boolean },
  stepAssembly: { tool: Schema.String, artifactId: Schema.String, passed: Schema.Boolean }
})
/** The working-level clauses of `InputValid`, as a host closure with no representation. */
const workingLevels = Schema.makeFilter((r: { readonly minimumLevelMm: number; readonly maximumLevelMm: number; readonly heightMm: number }) =>
  r.minimumLevelMm < r.maximumLevelMm && r.maximumLevelMm < r.heightMm
    ? undefined : { path: ["maximumLevelMm"], issue: "invalidWorkingLevels" })
const Levels = Schema.Struct({ heightMm: Nat, minimumLevelMm: Nat, maximumLevelMm: Nat })

const has = (needle: string) => (text: string) => text.includes(needle)

export const rows: ReadonlyArray<Row> = [
  // checks
  { id: "C1", construct: "a built-in filter with an id (Positive: isInt, isGreaterThan 0)", schema: Positive,
    samples: [3, 0, 1.5, -2], keptBy: has("effect/schema/isGreaterThan"),
    expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  { id: "C2", construct: "built-in filters with payloads (isNonEmpty, isBetween: the design reference)", schema: DesignRef,
    samples: [{ vesselId: "TK-101", revision: 3 }, { vesselId: "", revision: 3 }, { vesselId: "TK-101", revision: 0 }],
    keptBy: has("effect/schema/isBetween"), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  { id: "C2b", construct: "a filter group (isMinLength 1 and isMaxLength 64 on the vessel identifier)",
    schema: Schema.String.check(Schema.isMinLength(1).and(Schema.isMaxLength(64))), samples: ["TK-101", "", "x".repeat(65)],
    keptBy: has("\"FilterGroup\""), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  { id: "C3", construct: "a host closure filter with no id (the working levels)", schema: Levels.check(workingLevels),
    samples: [{ heightMm: 3000, minimumLevelMm: 300, maximumLevelMm: 2500 }, { heightMm: 3000, minimumLevelMm: 2500, maximumLevelMm: 300 }],
    keptBy: has("\"Filter\""), expect: { writes: false, kept: false, revives: false, sameDecoding: false, code: false } },
  { id: "C4", construct: "an aborting filter", schema: Schema.String.check(Schema.isNonEmpty().abort()),
    samples: ["a", ""], keptBy: has("\"aborted\":true"), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  { id: "C5", construct: "a refinement by a guard", schema: Schema.String.pipe(Schema.refine((s): s is `TK-${string}` => s.startsWith("TK-"))),
    samples: ["TK-101", "XX-1"], keptBy: has("\"Filter\""), expect: { writes: false, kept: false, revives: false, sameDecoding: false, code: false } },
  { id: "C6", construct: "a pattern filter (a regular expression)", schema: Schema.String.check(Schema.isPattern(/^[0-9a-f]{64}$/)),
    samples: ["a".repeat(64), "xyz"], keptBy: has("effect/schema/isPattern"), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  // brands
  { id: "B1", construct: "a brand (FlowRate)", schema: FlowRate, samples: [3, 0],
    keptBy: has("FlowRate"), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  // transformations
  { id: "T1", construct: "a built-in transformation (NumberFromString)", schema: Schema.NumberFromString,
    samples: ["1", " 1", "1e0", "abc", 1], keptBy: has("\"Number\""), expect: { writes: true, kept: false, revives: true, sameDecoding: false, code: true } },
  { id: "T2", construct: "a built-in transformation with a check (Trim)", schema: Schema.Trim,
    samples: ["a", " a "], keptBy: has("isTrimmed"), expect: { writes: true, kept: false, revives: true, sameDecoding: false, code: true } },
  { id: "T3", construct: "a host closure transformation (litres per minute to microlitres per second)",
    schema: Nat.pipe(Schema.decodeTo(Nat, SchemaTransformation.transform({
      decode: (lpm: number) => lpm * 1000000 / 60, encode: (uls: number) => uls * 60 / 1000000 }))),
    samples: [6, 7], keptBy: () => false, expect: { writes: true, kept: false, revives: true, sameDecoding: false, code: true } },
  { id: "T4", construct: "a data declaration with its own JSON codec (Date)", schema: Schema.Date,
    samples: ["2026-10-16T00:00:00.000Z"], keptBy: has("effect/schema/Date"), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  // defaults
  { id: "D1", construct: "a constructor default (the vessel's flow unit)",
    schema: Schema.Struct({ flowUnit: Unit.pipe(Schema.withConstructorDefault(Effect.succeed("microlitrePerSecond" as const))) }),
    samples: [{ flowUnit: "second" }, {}], keptBy: () => false, expect: { writes: true, kept: false, revives: true, sameDecoding: true, code: true } },
  { id: "D2", construct: "a decoding default at a key", schema: Schema.Struct({
      flowUnit: Unit.pipe(Schema.withDecodingDefaultKey(Effect.succeed("microlitrePerSecond" as const))) }),
    samples: [{ flowUnit: "second" }, {}], keptBy: () => false, expect: { writes: true, kept: false, revives: true, sameDecoding: false, code: true } },
  // optional keys
  { id: "O1", construct: "an optional key", schema: Schema.Struct({ note: Schema.optionalKey(Schema.String) }),
    samples: [{}, { note: "a" }, { note: undefined }], keptBy: has("\"isOptional\":true"), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  { id: "O2", construct: "an optional key that admits undefined", schema: Schema.Struct({ note: Schema.optional(Schema.String) }),
    samples: [{}, { note: "a" }, { note: undefined }], keptBy: has("\"Undefined\""), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  { id: "O3", construct: "a mutable key", schema: Schema.Struct({ level: Schema.mutableKey(Nat) }),
    samples: [{ level: 1 }], keptBy: has("\"isMutable\":true"), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  { id: "O4", construct: "an option read from null (OptionFromNullOr)", schema: Schema.Struct({ note: Schema.OptionFromNullOr(Schema.String) }),
    samples: [{ note: null }, { note: "a" }], keptBy: has("effect/schema/Option"), expect: { writes: true, kept: false, revives: true, sameDecoding: false, code: true } },
  // classes
  { id: "K1", construct: "a class (the design reference as Schema.Class)",
    schema: class DesignRefClass extends Schema.Class<DesignRefClass>("DesignRef")({ vesselId: Schema.String, revision: Nat }) {},
    samples: [{ vesselId: "TK-101", revision: 3 }], keptBy: has("DesignRef"), expect: { writes: true, kept: true, revives: true, sameDecoding: false, code: true } },
  // unions
  { id: "U1", construct: "a literal union of eight members (Unit)", schema: Unit, samples: ["metre", "furlong"],
    keptBy: has("\"Union\""), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  { id: "U2", construct: "a literal union of two members (LevelDatum)", schema: LevelDatum, samples: ["internalBottom", "x"],
    keptBy: has("\"Union\""), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  { id: "U3", construct: "a tagged union of three cases (Evidence)", schema: Evidence,
    samples: [{ _tag: "geometry", tool: "cad", artifactId: "a1", passed: true }, { _tag: "other", tool: "cad", artifactId: "a1", passed: true }],
    keptBy: has("\"_tag\""), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  { id: "U4", construct: "a oneOf union", schema: Schema.Union([Schema.String, Schema.String.check(Schema.isNonEmpty())], { mode: "oneOf" }),
    samples: ["", "a"], keptBy: has("\"oneOf\""), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } },
  { id: "U5", construct: "a number literal and a Boolean literal", schema: Schema.Literals([1, true]), samples: [1, true, 2],
    keptBy: has("\"number\""), expect: { writes: true, kept: true, revives: true, sameDecoding: true, code: true } }
]

if (import.meta.main) {
  void evidenceKinds
  void Option
  const checkRevivers = builtins.filter(r => r.id.startsWith("effect/schema/is"))
  say(`revivers: ${builtins.length}: ${checkRevivers.length} checks, ${builtins.length - checkRevivers.length} declarations`)
  runRows(rows)
  // T4: a fixed declaration is data with a JSON codec, not a host object
  const date = decode(Schema.toCodecJson(Schema.Date), "2026-10-16T00:00:00.000Z")
  say(`T4 Date through its JSON codec: ${"ok" in date && date.ok instanceof globalThis.Date ? "decodes the ISO string to a Date" : show(date)}`)
  // T1, the pair's two directions: a widening on read, and no retraction at negative zero.
  const nfs = Schema.NumberFromString
  say(`T1 read: ${show(["1", " 1", "1e0", "abc", ""].map(s => decode(nfs, s)))}`)
  say(`T1 write then read at -0: ${show(encode(nfs, -0))} reads ${show(decode(nfs, "0"))}`)
  say(`T1 write then read at NaN: ${show(encode(nfs, NaN))} reads ${show(decode(nfs, "NaN"))}`)
  // T2: a widening on read; the retraction holds on trimmed strings.
  say(`T2 read: ${JSON.stringify([" a ", "a"].map(s => decode(Schema.Trim, s)))}; write "a": ${JSON.stringify(encode(Schema.Trim, "a"))}`)
  // The type side's document of a transformation: the target alone.
  say(`T1 type side: ${show(typeDocOf(nfs))}`)
  say(`K1 type side: ${show(typeDocOf(rows.find(r => r.id === "K1")!.schema))}`)
  const k1 = rows.find(r => r.id === "K1")!.schema
  const k1Decoded = decode(k1, { vesselId: "TK-101", revision: 3 })
  say(`K1 the original decodes to a class instance: ${"ok" in k1Decoded && Object.getPrototypeOf(k1Decoded.ok) !== Object.prototype}`)
  finish("census")
}
