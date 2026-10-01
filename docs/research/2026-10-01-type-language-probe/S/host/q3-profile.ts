// Seat S, question 3: the readable profile's emissions against rc.112 (bun, vendored source).
// Reads the EXPR_/REPR_ lines of logs/readable.log (Lean's readable text and Lean's raw persisted
// document for the same Representation). For every admitted example:
//  (1) representation: rc.112's persisted form of the evaluated readable text equals Lean's
//      document modulo nS (annotations erased, anyOf right spine flattened, properties compared as
//      a set: rc.112 puts integer-like names first, question 2 E8p);
//  (2) decoding: the evaluated readable schema and rc.112's own revival of Lean's document
//      (fromRepresentation with the two built-in revivers) accept and answer alike, under the
//      default and the strict excess-property options.
// It also writes generated-profile.ts (the emitted module) for the tsgo type controls.
import { deepStrictEqual } from "node:assert"
import { readFileSync, writeFileSync } from "node:fs"
import * as Schema from "effect/Schema"
import * as SR from "effect/SchemaRepresentation"

const RED = (globalThis as any).process?.env?.Q3_RED === "1"
const log = readFileSync(new URL("../logs/readable.log", import.meta.url), "utf8")
const ex: Record<string, { expr: string; repr: string }> = {}
for (const line of log.split("\n")) {
  const m = /^(EXPR|REPR)_([A-Z0-9_]+):(.*)$/.exec(line)
  if (!m) continue
  const e = (ex[m[2]!] ??= { expr: "", repr: "" })
  if (m[1] === "EXPR") e.expr = JSON.parse(m[3]!)
  else e.repr = JSON.parse(m[3]!)
}

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
const revivers = [Schema.isIntReviver, Schema.isGreaterThanOrEqualToReviver]
const evalExpr = (t: string) => Function("Schema", `return (${t})`)(Schema)
const evalRepr = (t: string) => Function(`return (${t})`)()
type Obs = { accepted: true; value: unknown } | { accepted: false }
function observe(s: any, v: unknown, options?: any): Obs {
  try { return { accepted: true, value: Schema.decodeUnknownSync(s, options)(v) } } catch { return { accepted: false } }
}
const P = (t: string) => JSON.parse(t)
const inputs: Record<string, unknown[]> = {
  NAT: [0, 42, -1, 1.5, "42", Number.MAX_SAFE_INTEGER + 1, -0],
  INT: [0, -15, 1.5, "1", 2 ** 53],
  RECORD: [{ a: 1, b: "x" }, { b: "x", a: 1 }, { a: 1 }, { a: "1", b: "x" }, { a: 1, b: "x", c: true }, { a: 1.5, b: "x" }],
  OPTIONAL: [{ b: "x" }, { a: 1, b: "x" }, { a: undefined, b: "x" }, { a: null, b: "x" }],
  OPTIONAL_UNDEF: [{}, { a: 1 }, { a: undefined }, { a: null }],
  MAP: [{}, { a: 1, b: 2 }, { a: "x" }, { a: 1.5 }, P('{"a":1,"a":2}')],
  TAGGED2: [{ _tag: "A", x: 1 }, { _tag: "B", y: "s" }, { _tag: "A", y: "s" }, {}],
  TAGGED3: [{ _tag: "A", x: 1 }, { _tag: "B", y: "s" }, { _tag: "C" }, { _tag: "D" }, { _tag: "C", x: 1 }],
  LIT3_NESTED: ["a", "b", "c", "d", 1],
  LIT3_FLAT: ["a", "b", "c", "d", 1],
  TUPLE3: [[1, "x", true], [1, "x"], [1, "x", true, 0], ["1", "x", true]],
  ARRAY: [[], ["a", "b"], [1]],
  NESTED: [{ user: { age: 42, name: "Sam" } }, { user: { age: -1, name: "Sam" } }, { user: { age: 1 } }],
  SPECIAL: [P('{"__proto__":1,"a-b":"x","é":true,"constructor":"c","":2,"10":3,"9":4}'),
    P('{"a-b":"x","é":true,"constructor":"c","":2,"10":3,"9":4}'),
    P('{"__proto__":1,"a-b":"x","é":true,"constructor":"c","":2,"10":3,"9":-4}')],
  ESCAPED: [P('{"x\\"y":"s","a":1}'), { a: 1 }],
  MUTABLE: [{}, { "a-b": "ok" }, { "a-b": undefined }, { "a-b": 1 }],
}
const refused = ["ESC_PROTO", "MAP_NUMBER", "REST", "RC_INT"]

let failures = 0, comparisons = 0
function check(what: string, actual: unknown, expected: unknown) {
  let ok = true
  try { deepStrictEqual(actual, expected) } catch { ok = false }
  if (!ok) failures++
  console.log(`${ok ? "ok  " : "FAIL"} ${what}${ok ? "" : ` :: actual=${JSON.stringify(actual)} expected=${JSON.stringify(expected)}`}`)
}
const exportsTs: string[] = []
for (const [name, { expr, repr }] of Object.entries(ex)) {
  if (refused.includes(name)) {
    check(`${name}: no code is emitted (Lean refuses)`, expr, "REFUSED")
    continue
  }
  const S = evalExpr(expr)
  exportsTs.push(`export const ${name} = ${expr};`)
  const lean = evalRepr(repr)
  const doc = SR.fromJson({ representation: lean, references: {} } as any)
  const revived = SR.fromRepresentation(doc, { revivers })
  const persisted = (SR.toJson(SR.toRepresentation(S.ast)) as any).representation
  const leanJson = (SR.toJson(doc) as any).representation
  check(`${name}: rc.112's persisted form of the readable text equals Lean's document modulo nS`,
    nS(persisted), RED && name === "TUPLE3" ? nS((SR.toJson(SR.toRepresentation(Schema.Array(Schema.Int).ast)) as any).representation) : nS(leanJson))
  for (const options of [undefined, { onExcessProperty: "error" }]) {
    for (const v of inputs[name] ?? []) {
      comparisons++
      check(`${name}: decode ${JSON.stringify(v)} ${options ? "strict" : "default"}`, observe(S, v, options), observe(revived, v, options))
    }
  }
}
// rc.112 itself revives the document the profile refuses for its `arbitrary` annotation
const rcInt = SR.fromRepresentation(SR.fromJson({ representation: evalRepr(ex["RC_INT"]!.repr), references: {} } as any), { revivers })
check("RC_INT: rc.112 revives its own document (the profile's refusal is the allowlist's)", observe(rcInt, 3), { accepted: true, value: 3 })
writeFileSync(new URL("./generated-profile.ts", import.meta.url),
  `// GENERATED by S/host/q3-profile.ts from logs/readable.log (Lean's readable profile); do not edit\nimport * as Schema from "effect/Schema"\n${exportsTs.join("\n")}\n`)
console.log(`SUMMARY examples=${Object.keys(ex).length} decode-comparisons=${comparisons} failures=${failures}${RED ? " (red twin)" : ""}`)
if (failures > 0) (globalThis as any).process.exit(1)
