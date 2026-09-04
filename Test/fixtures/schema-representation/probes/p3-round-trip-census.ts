/**
 * PROBE 3 — per-tag round trip over the frozen 22-tag census.
 *
 * Executes effect@4.0.0-rc.112. Every row is an OBSERVATION.
 *
 * For each census tag this probe tries, in order:
 *   (i)  build a schema from the PUBLIC `Schema` API whose emitted document
 *        actually contains a node with that `_tag`;
 *   (ii) emit  toJson(toRepresentation(schema.ast))  and stringify it;
 *   (iii) round trip the TEXT:  text -> JSON.parse -> fromJson -> toJson
 *        -> JSON.stringify, and compare bytes.
 *
 * A tag that cannot be reached from the public API is recorded as such, and
 * then exercised by hand-writing the node and running only step (iii).
 */
import { Schema, SchemaRepresentation } from "effect"

const CENSUS = [
  "Declaration", "Reference", "Suspend",
  "Null", "Undefined", "Void", "Never", "Unknown", "Any",
  "String", "Number", "Boolean", "BigInt", "Symbol",
  "Literal", "UniqueSymbol", "ObjectKeyword", "Enum",
  "TemplateLiteral", "Arrays", "Objects", "Union",
] as const

const docOf = (schema: Schema.Top) =>
  SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(schema.ast))

const tagsIn = (value: unknown): Array<string> => {
  const out: Array<string> = []
  const walk = (v: unknown): void => {
    if (Array.isArray(v)) { for (const i of v) walk(i); return }
    if (typeof v !== "object" || v === null) return
    const n = v as Record<string, unknown>
    if (typeof n["_tag"] === "string") out.push(n["_tag"] as string)
    for (const c of Object.values(n)) walk(c)
  }
  walk(value)
  return out
}

const roundTripText = (text: string): { ok: boolean; out: string } => {
  try {
    const out = JSON.stringify(
      SchemaRepresentation.toJson(SchemaRepresentation.fromJson(JSON.parse(text))),
    )
    return { ok: out === text, out }
  } catch (e) {
    return { ok: false, out: `THREW ${(e as Error).constructor.name}: ${String((e as Error).message).split("\n")[0]}` }
  }
}

interface Row {
  tag: string
  route: string
  constructed: boolean
  tagPresent: boolean | "n/a"
  emitted: string
  roundTripIdentical: boolean
  roundTripOut: string
  note: string
}

const rows: Array<Row> = []

const fromSchema = (tag: string, route: string, build: () => Schema.Top, note = ""): void => {
  try {
    const schema = build()
    const json = docOf(schema)
    const text = JSON.stringify(json)
    const present = tagsIn(json).includes(tag)
    const rt = roundTripText(text)
    rows.push({
      tag, route, constructed: true, tagPresent: present,
      emitted: text, roundTripIdentical: rt.ok, roundTripOut: rt.out, note,
    })
  } catch (e) {
    rows.push({
      tag, route, constructed: false, tagPresent: false, emitted: "",
      roundTripIdentical: false, roundTripOut: "",
      note: `${note} BUILD THREW ${(e as Error).constructor.name}: ${String((e as Error).message).split("\n")[0]}`,
    })
  }
}

const fromHandWritten = (tag: string, route: string, document: unknown, note: string): void => {
  const text = JSON.stringify(document)
  const rt = roundTripText(text)
  rows.push({
    tag, route, constructed: false, tagPresent: "n/a",
    emitted: text, roundTripIdentical: rt.ok, roundTripOut: rt.out, note,
  })
}

const wrap = (rep: unknown) => ({ representation: rep, references: {} })
const kw = (t: string) => ({ _tag: t, checks: [] })

/* ---------------------------------------------------------------- keywords */
fromSchema("Null", "Schema.Null", () => Schema.Null)
fromSchema("Undefined", "Schema.Undefined", () => Schema.Undefined)
fromSchema("Void", "Schema.Void", () => Schema.Void)
fromSchema("Never", "Schema.Never", () => Schema.Never)
fromSchema("Unknown", "Schema.Unknown", () => Schema.Unknown)
fromSchema("Any", "Schema.Any", () => Schema.Any)
fromSchema("String", "Schema.String", () => Schema.String)
fromSchema("Number", "Schema.Number", () => Schema.Number)
fromSchema("Boolean", "Schema.Boolean", () => Schema.Boolean)
fromSchema("BigInt", "Schema.BigInt", () => Schema.BigInt)
fromSchema("Symbol", "Schema.Symbol", () => Schema.Symbol)
fromSchema("ObjectKeyword", "Schema.ObjectKeyword", () => Schema.ObjectKeyword)

/* ---------------------------------------------------------------- structural */
fromSchema("Literal", "Schema.Literal(\"a\")", () => Schema.Literal("a"))
fromSchema("Literal", "Schema.Literal(1)", () => Schema.Literal(1))
fromSchema("Literal", "Schema.Literal(1n)", () => Schema.Literal(1n))
fromSchema("Literal", "Schema.Literal(true)", () => Schema.Literal(true))
fromSchema("UniqueSymbol", "Schema.UniqueSymbol(Symbol.for(\"effect4/probe\"))",
  () => Schema.UniqueSymbol(globalThis.Symbol.for("effect4/probe")))
// A LOCAL symbol: the schema BUILDS, and fails only at emission. Recorded
// separately so the failure point is not guessed.
{
  const local = Schema.UniqueSymbol(globalThis.Symbol("local"))
  rows.push({
    tag: "UniqueSymbol", route: "Schema.UniqueSymbol(Symbol(\"local\"))  [LOCAL symbol]",
    constructed: true, tagPresent: "n/a", emitted: "",
    roundTripIdentical: false, roundTripOut: "",
    note: `schema BUILT, ast._tag = ${(local as any).ast._tag}; emission: ${
      (() => { try { docOf(local); return "SUCCEEDED" } catch (e) { return `THREW ${(e as Error).constructor.name}: ${String((e as Error).message).split("\n")[0]}` } })()
    }`,
  })
}
fromSchema("Enum", "Schema.Enum({ A: \"a\", B: 2 })", () => Schema.Enum({ A: "a", B: 2 } as any))
fromSchema("TemplateLiteral", "Schema.TemplateLiteral([\"id-\", Schema.String])",
  () => Schema.TemplateLiteral(["id-", Schema.String]))
fromSchema("Arrays", "Schema.Array(Schema.String)", () => Schema.Array(Schema.String))
fromSchema("Arrays", "Schema.Tuple([Schema.String, Schema.Number])",
  () => Schema.Tuple([Schema.String, Schema.Number]))
fromSchema("Arrays", "Schema.TupleWithRest(Schema.Tuple([Schema.String]), [Schema.Number])",
  () => Schema.TupleWithRest(Schema.Tuple([Schema.String]), [Schema.Number]))
fromSchema("Objects", "Schema.Struct({ a: Schema.String })", () => Schema.Struct({ a: Schema.String }))
fromSchema("Objects", "Schema.Record(Schema.String, Schema.Number)  [index signature]",
  () => Schema.Record(Schema.String, Schema.Number))
fromSchema("Union", "Schema.Union([Schema.String, Schema.Number])",
  () => Schema.Union([Schema.String, Schema.Number]))
fromSchema("Union", "Schema.Union([...], { mode: \"oneOf\" })",
  () => Schema.Union([Schema.String, Schema.Number], { mode: "oneOf" }))

/* ---------------------------------------------------------------- recursion */
interface Node { readonly v: string; readonly next: Node | null }
const NodeSchema: any = Schema.Struct({
  v: Schema.String,
  next: Schema.suspend((): any => Schema.NullOr(NodeSchema)),
})
fromSchema("Suspend", "Schema.suspend(() => Schema.String)",
  () => Schema.suspend((): Schema.Codec<string> => Schema.String))
fromSchema("Reference", "recursive Struct with Schema.suspend", () => NodeSchema)

/* ---------------------------------------------------------------- declaration */
for (const [route, build] of [
  ["Schema.Date", () => Schema.Date],
  ["Schema.Option(Schema.String)", () => Schema.Option(Schema.String)],
  ["Schema.URL", () => Schema.URL],
  ["Schema.Json", () => Schema.Json],
  ["Schema.Uint8Array", () => Schema.Uint8Array],
] as Array<[string, () => Schema.Top]>) {
  fromSchema("Declaration", route, build)
}

/* ---------------------------------------------------------------- checks */
fromSchema("Filter (check)", "Schema.String.check(Schema.isMinLength(3))",
  () => Schema.String.check(Schema.isMinLength(3)))
fromSchema("Filter (check)", "Schema.Number.check(Schema.isInt())",
  () => Schema.Number.check(Schema.isInt()))
fromSchema("Filter (check)", "Schema.String.check(Schema.isUUID())",
  () => Schema.String.check(Schema.isUUID()))
fromSchema("Filter (check)", "Schema.Number.check(Schema.isBetween({minimum:1,maximum:5}))",
  () => Schema.Number.check(Schema.isBetween({ minimum: 1, maximum: 5 })))
fromSchema("FilterGroup (check)", "Schema.String.check(Schema.makeFilterGroup([isMinLength(2), isMaxLength(5)]))",
  () => Schema.String.check(
    Schema.makeFilterGroup([Schema.isMinLength(2), Schema.isMaxLength(5)] as any) as any,
  ),
  "the ONLY route found to a FilterGroup; note the emitted FilterGroup carries NO `representation`")
// A check payload holding a non-finite number: a THIRD numeric domain, beyond
// the two the ruling names.
rows.push({
  tag: "Filter (check)", route: "Schema.isBetween({minimum:1,maximum:Infinity})",
  constructed: false, tagPresent: "n/a", emitted: "", roundTripIdentical: false, roundTripOut: "",
  note: (() => {
    try { docOf(Schema.Number.check(Schema.isBetween({ minimum: 1, maximum: Infinity }))); return "SUCCEEDED" }
    catch (e) { return `THREW ${(e as Error).constructor.name}: ${String((e as Error).message).split("\n")[0]}` }
  })(),
})

/* ---------------------------------------------------------------- hand-written */
fromHandWritten("Never", "hand-written Never with a check",
  wrap({ _tag: "Never", checks: [{ _tag: "Filter", representation: { id: "x", payload: null }, aborted: false }] }),
  "does a Never node accept a check?")
fromHandWritten("Reference", "hand-written dangling $ref",
  { representation: { _tag: "Reference", $ref: "Nope" }, references: {} },
  "dangling reference, per E4-SCHEMA-CE-025")
fromHandWritten("Declaration", "hand-written minimal Declaration",
  wrap({ _tag: "Declaration", representation: { id: "probe/decl", payload: null }, typeParameters: [], checks: [] }),
  "minimal Declaration with required representation")
fromHandWritten("Declaration", "hand-written Declaration WITHOUT representation",
  wrap({ _tag: "Declaration", typeParameters: [], checks: [] }),
  "the codec requires `representation` even though the interface marks it optional")
fromHandWritten("Suspend", "hand-written Suspend with a non-empty checks",
  wrap({ _tag: "Suspend", checks: [{ _tag: "Filter", representation: { id: "x", payload: null }, aborted: false }], thunk: kw("String") }),
  "Suspend.checks is Tuple([])")

/* ---------------------------------------------------------------- report */
console.log(`runtime effect@${
  (await import("effect/package.json", { with: { type: "json" } })).default.version
}`)
console.log("")
for (const r of rows) {
  console.log(`### ${r.tag}  <=  ${r.route}`)
  console.log(`constructed        : ${r.constructed}`)
  console.log(`tag present in doc : ${r.tagPresent}`)
  console.log(`emitted            :${r.emitted === "" ? "" : ` ${r.emitted}`}`)
  console.log(`round trip == bytes: ${r.roundTripIdentical}`)
  if (!r.roundTripIdentical) {
    console.log(`round trip out     :${r.roundTripOut === "" ? "" : ` ${r.roundTripOut}`}`)
  }
  if (r.note) console.log(`note               : ${r.note}`)
  console.log("")
}
const reached = new Set(rows.filter((r) => r.tagPresent === true).map((r) => r.tag))
console.log("### census coverage from the public Schema API")
for (const tag of CENSUS) console.log(`${tag.padEnd(18)} reachable-from-public-API: ${reached.has(tag)}`)
