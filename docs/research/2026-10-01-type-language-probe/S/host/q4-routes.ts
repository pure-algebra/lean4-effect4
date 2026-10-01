// Seat S, question 4: the two routes to readable Schema text, compared on the same documents.
//  Route L (Lean): the readable profile's text (logs/readable.log, EXPR_ lines).
//  Route U (upstream, Codex's reuse.mjs extended): Lean's persisted document (REPR_ lines) ->
//    SchemaRepresentation.fromJson -> fromRepresentation with a pinned reviver list ->
//    toRepresentation -> toCodeDocument (rc.112's public API, vendored source under bun).
// For each example: coverage (code or a refusal), source size, the representation modulo nS, and
// decoder agreement against the reference R = rc.112's own revival of Lean's document, under the
// default and the strict excess-property options. Names are split ordinary / adversarial.
// Writes upstream-generated.ts (route U's runtime and Type texts) for the tsgo comparison.
import { deepStrictEqual } from "node:assert"
import { readFileSync, writeFileSync } from "node:fs"
import * as O from "effect/Option"
import * as Res from "effect/Result"
import * as Schema from "effect/Schema"
import * as SR from "effect/SchemaRepresentation"

const RED = (globalThis as any).process?.env?.Q4_RED === "1"
const log = readFileSync(new URL("../logs/readable.log", import.meta.url), "utf8")
const ex: Record<string, { expr: string; repr: string }> = {}
for (const line of log.split("\n")) {
  const m = /^(EXPR|REPR)_([A-Z0-9_]+):(.*)$/.exec(line)
  if (!m) continue
  const e = (ex[m[2]!] ??= { expr: "", repr: "" })
  if (m[1] === "EXPR") e.expr = JSON.parse(m[3]!)
  else e.repr = JSON.parse(m[3]!)
}
const adversarial = new Set(["SPECIAL", "ESCAPED", "ESC_PROTO", "N_PROTO", "N_HYPHEN", "N_UNICODE",
  "N_RESERVED", "N_EMPTY", "N_NUMERIC", "N_QUOTE", "MUTABLE"])
// the pinned reviver list: the two checks Bridge.schema writes, and the declarations it writes
const revivers = [Schema.isIntReviver, Schema.isGreaterThanOrEqualToReviver, Schema.OptionReviver,
  Schema.ResultReviver, Schema.ExitReviver, Schema.CauseReviver, Schema.Uint8ArrayReviver,
  Schema.JsonReviver]
// Lean's `Bridge.defectRep` writes `effect/schema/Defect`, an id rc.112 never writes (its defect
// slot persists as `effect/schema/Json`: q4-defect.ts); EXIT_AS_RC is Lean's EXIT with rc.112's id
ex["EXIT_AS_RC"] = { expr: "REFUSED", repr: ex["EXIT"]!.repr.replaceAll("effect/schema/Defect", "effect/schema/Json") }

const utf8 = (s: string) => Array.from(new TextEncoder().encode(s))
function cmpBytes(a: string, b: string): number {
  const x = utf8(a), y = utf8(b)
  for (let i = 0; i < Math.min(x.length, y.length); i++) if (x[i] !== y[i]) return x[i]! - y[i]!
  return x.length - y.length
}
function nS(r: any): any {
  if (Array.isArray(r)) return r.map(nS)
  if (r === null || typeof r !== "object") return r
  const out: any = {}
  for (const [k, v] of Object.entries(r)) { if (k !== "annotations") out[k] = nS(v) }
  if (out._tag === "Union" && out.mode === "anyOf" && out.checks.length === 0) {
    const last = out.types[out.types.length - 1]
    if (last && last._tag === "Union" && last.mode === "anyOf" && last.checks.length === 0)
      out.types = [...out.types.slice(0, -1), ...last.types]
  }
  if (out._tag === "Objects")
    out.propertySignatures = [...out.propertySignatures].sort((a: any, b: any) =>
      cmpBytes(String(a.name.value), String(b.name.value)))
  return out
}
const evalExpr = (t: string) => Function("Schema", `return (${t})`)(Schema)
const evalRepr = (t: string) => Function(`return (${t})`)()
type Obs = { accepted: true; value: unknown } | { accepted: false }
function observe(s: any, v: unknown, options?: any): Obs {
  try { return { accepted: true, value: Schema.decodeUnknownSync(s, options)(v) } } catch { return { accepted: false } }
}
const same = (a: unknown, b: unknown) => { try { deepStrictEqual(a, b); return true } catch { return false } }
const persisted = (s: any) => nS((SR.toJson(SR.toRepresentation(s.ast)) as any).representation)
const P = (t: string) => JSON.parse(t)
const inputs: Record<string, unknown[]> = {
  NAT: [0, 42, -1, 1.5, "42", Number.MAX_SAFE_INTEGER + 1, -0],
  INT: [0, -15, 1.5, "1", 2 ** 53],
  RECORD: [{ a: 1, b: "x" }, { b: "x", a: 1 }, { a: 1 }, { a: "1", b: "x" }, { a: 1, b: "x", c: true }],
  OPTIONAL: [{ b: "x" }, { a: 1, b: "x" }, { a: undefined, b: "x" }, { a: null, b: "x" }],
  OPTIONAL_UNDEF: [{}, { a: 1 }, { a: undefined }, { a: null }],
  MAP: [{}, { a: 1, b: 2 }, { a: "x" }, { a: 1.5 }],
  TAGGED2: [{ _tag: "A", x: 1 }, { _tag: "B", y: "s" }, { _tag: "A", y: "s" }, {}],
  TAGGED3: [{ _tag: "A", x: 1 }, { _tag: "B", y: "s" }, { _tag: "C" }, { _tag: "D" }],
  LIT3_NESTED: ["a", "b", "c", "d", 1],
  LIT3_FLAT: ["a", "b", "c", "d", 1],
  TUPLE3: [[1, "x", true], [1, "x"], [1, "x", true, 0]],
  ARRAY: [[], ["a", "b"], [1]],
  NESTED: [{ user: { age: 42, name: "Sam" } }, { user: { age: -1, name: "Sam" } }, { user: { age: 1 } }],
  SPECIAL: [P('{"__proto__":1,"a-b":"x","é":true,"constructor":"c","":2,"10":3,"9":4}'),
    P('{"a-b":"x","é":true,"constructor":"c","":2,"10":3,"9":4}')],
  ESCAPED: [P('{"x\\"y":"s","a":1}'), { a: 1 }],
  MUTABLE: [{}, { "a-b": "ok" }, { "a-b": undefined }, { "a-b": 1 }],
  N_PROTO: [P('{"__proto__":1}'), {}, P('{"__proto__":"x"}')],
  N_HYPHEN: [{ "a-b": "x" }, {}, { "a-b": 1 }],
  N_UNICODE: [{ "é": true, "日本": 1, "😀": "x" }, { "é": true, "日本": 1 }],
  N_RESERVED: [{ constructor: "c", toString: "t", default: 1, class: true }, {}],
  N_EMPTY: [{ "": 1 }, {}, { "": "x" }],
  N_NUMERIC: [{ "01": 1, "10": 2, "9": 3, "1e3": 4 }, { "01": 1, "10": 2, "9": 3 }],
  N_QUOTE: [P('{"x\\"y":"s","line\\nbreak":1}'), { "x\"y": "s" }],
  // the examples only route U emits: its decoders against the reference
  MAP_NUMBER: [{}, { "1": 2 }, { "a": 2 }, { "1": "x" }],
  REST: [{ a: 1 }, { a: 1, b: 2 }, { a: 1, b: "x" }, {}],
  RC_INT: [1, 1.5, -2],
  OPTION: [O.some(1), O.none(), O.some(1.5), 1],
  RESULT: [Res.succeed(1), Res.fail("e"), Res.succeed("x"), 1],
  BYTES: [new Uint8Array([1, 2]), "x", [1, 2]],
}
type Row = { name: string; kind: string; lean: string; upstream: string; leanBytes: number | null;
  upstreamBytes: number | null; upstreamTypeBytes: number | null; leanRepr: string; upstreamRepr: string;
  leanDecode: string; upstreamDecode: string }
const rows: Row[] = []
const upstreamTs: string[] = []
const upstreamImports = new Set<string>()
const upstreamTypes: string[] = []
let checks = 0, failures = 0
for (const [name, { expr, repr }] of Object.entries(ex)) {
  const kind = adversarial.has(name) ? "adversarial" : "ordinary"
  const doc = SR.fromJson({ representation: evalRepr(repr), references: {} } as any)
  let reference: any = null, refErr = ""
  try { reference = SR.fromRepresentation(doc, { revivers }) } catch (e: any) { refErr = String(e?.message ?? e).split("\n")[0]! }
  let code: { runtime: string; Type: string } | null = null, upErr = ""
  if (reference !== null) {
    try {
      const cd = SR.toCodeDocument(SR.toMultiDocument(SR.toRepresentation(reference.ast)))
      code = cd.codes[0] as any
      for (const a of cd.artifacts) if (a._tag === "Import") upstreamImports.add(a.importDeclaration)
    }
    catch (e: any) { upErr = String(e?.message ?? e).replace(/\n\s*/g, " ") }
  } else upErr = `fromRepresentation: ${refErr}`
  const L = expr === "REFUSED" ? null : evalExpr(expr)
  let U: any = null
  if (code) { try { U = evalExpr(code.runtime) } catch (e: any) { upErr = `eval: ${e?.name}` } }
  if (code) { upstreamTs.push(`export const ${name} = ${code.runtime};`); upstreamTypes.push(`export type ${name}_T = ${code.Type};`) }
  const leanDoc = nS((SR.toJson(doc) as any).representation)
  const reprOf = (s: any) => s === null ? "—" : same(persisted(s), RED && name === "RECORD" && s === L ? null : leanDoc) ? "equal" : "differs"
  let lAgree = 0, lTotal = 0, uAgree = 0, uTotal = 0
  if (reference !== null) for (const options of [undefined, { onExcessProperty: "error" }]) for (const v of inputs[name] ?? []) {
    const r = observe(reference, v, options)
    if (L) { lTotal++; if (same(observe(L, v, options), r)) lAgree++ }
    if (U) { uTotal++; if (same(observe(U, v, options), r)) uAgree++ }
  }
  const row: Row = { name, kind, lean: expr === "REFUSED" ? "refused" : "code", upstream: code ? "code" : `refused (${upErr})`,
    leanBytes: L ? utf8(expr).length : null, upstreamBytes: code ? utf8(code.runtime).length : null,
    upstreamTypeBytes: code ? utf8(code.Type).length : null, leanRepr: reprOf(L), upstreamRepr: reprOf(U),
    leanDecode: L ? `${lAgree}/${lTotal}` : "—", upstreamDecode: U ? `${uAgree}/${uTotal}` : "—" }
  rows.push(row)
  console.log(`ROW ${JSON.stringify(row)}`)
  if (code) console.log(`UPSTREAM_${name}: ${code.runtime}`)
  // the expectations this harness asserts (the comparison is the table; these keep it honest)
  checks++
  if (L && !(row.leanRepr === "equal" && lAgree === lTotal)) { failures++; console.log(`FAIL ${name}: route L disagrees with the reference`) }
}
// the asserted differences, each a finding: upstream loses an own `__proto__` field
const protoRow = rows.find((r) => r.name === "N_PROTO")!
checks++
if (!(protoRow.upstreamRepr === "differs" && protoRow.upstreamDecode !== `${(inputs.N_PROTO!.length) * 2}/${(inputs.N_PROTO!.length) * 2}`)) {
  failures++; console.log("FAIL N_PROTO: expected route U to lose the __proto__ field")
}
writeFileSync(new URL("./upstream-generated.ts", import.meta.url),
  `// GENERATED by S/host/q4-routes.ts (route U: rc.112's toCodeDocument on Lean's documents); do not edit\nimport * as Schema from "effect/Schema"\n${[...upstreamImports].join("\n")}\n${upstreamTs.join("\n")}\n`)
writeFileSync(new URL("./upstream-types.ts", import.meta.url),
  `// GENERATED by S/host/q4-routes.ts (route U's Type texts); do not edit\nimport * as Schema from "effect/Schema"\n${[...upstreamImports].join("\n")}\n${upstreamTypes.join("\n")}\n`)
console.log(`UPSTREAM_IMPORTS ${JSON.stringify([...upstreamImports])}`)
const by = (k: string) => rows.filter((r) => r.kind === k)
for (const k of ["ordinary", "adversarial"]) {
  const rs = by(k)
  const covL = rs.filter((r) => r.lean === "code").length, covU = rs.filter((r) => r.upstream === "code").length
  const exactL = rs.filter((r) => r.lean === "code" && r.leanRepr === "equal" && r.leanDecode.split("/")[0] === r.leanDecode.split("/")[1]).length
  const exactU = rs.filter((r) => r.upstream === "code" && r.upstreamRepr === "equal" && r.upstreamDecode.split("/")[0] === r.upstreamDecode.split("/")[1]).length
  const bytesL = rs.reduce((n, r) => n + (r.leanBytes ?? 0), 0), bytesU = rs.reduce((n, r) => n + (r.upstreamBytes ?? 0), 0)
  console.log(`SUMMARY_${k} examples=${rs.length} codeL=${covL} codeU=${covU} faithfulL=${exactL} faithfulU=${exactU} bytesL=${bytesL} bytesU=${bytesU}`)
}
const both = rows.filter((r) => r.lean === "code" && r.upstream === "code")
console.log(`SUMMARY_common examples=${both.length} bytesL=${both.reduce((n, r) => n + r.leanBytes!, 0)} bytesU=${both.reduce((n, r) => n + r.upstreamBytes!, 0)} typeBytesU=${both.reduce((n, r) => n + r.upstreamTypeBytes!, 0)}`)
writeFileSync(new URL("./q4-types-auto.ts", import.meta.url),
  `// GENERATED by S/host/q4-routes.ts: route U's own Type text against the inferred type of its runtime text\nimport * as U from "./upstream-generated.ts"\nimport type * as T from "./upstream-types.ts"\ntype Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends (<T>() => T extends B ? 1 : 2) ? true : false\ntype Assert<T extends true> = T\n` +
  rows.filter((r) => r.upstream === "code").map((r) => `export type ${r.name} = Assert<Equal<typeof U.${r.name}.Type, T.${r.name}_T>>`).join("\n") + "\n")
console.log(`SUMMARY checks=${checks} failures=${failures}${RED ? " (red twin)" : ""}`)
if (failures > 0) (globalThis as any).process.exit(1)
