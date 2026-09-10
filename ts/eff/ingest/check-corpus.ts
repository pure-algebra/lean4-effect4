// Exact fixture gate. Parser children are bounded to 500 files by their parent.
import { readFileSync, readdirSync } from "node:fs"
import { spawnSync } from "node:child_process"
import { join, basename } from "node:path"
import { isDeepStrictEqual } from "node:util"
import * as ck from "./ck.ts"
import * as oxc from "./oxc.ts"
import { effJson } from "../json.gen.ts"
import { encodeProgram } from "../wire.gen.ts"
import { compareVerdicts } from "./gate.ts"

const [mode, dir, offset = "0", count = "500"] = process.argv.slice(2)
if (!dir) throw new Error("check-corpus.ts printed|foreign|inclusion|printed-batch|foreign-batch|inclusion-batch <directory> [offset] [count]")

// ---- the inclusion property (DI-37) --------------------------------------------------
// The two ingest contracts differ on three axes: the admitted language, the refusal
// discipline, and the service-key numbering — a foreign lift renumbers keys from 4 in
// first-seen order (`ck.ts` `this.keys.length + 4`, `oxc.ts` the same), while a printed image
// carries the ordinals Lean minted. The claim under test is that the printed image is a
// sub-language of the foreign one: every printed module the foreign contract admits must lift
// to the program the printed oracle names, *up to that renumbering*.
//
// The numbering axis is taken out by canonical renumbering rather than by asserting either
// base: every `{name:{value},service:{value}}` node is rewritten with its first-seen index, on
// both sides. The bases actually observed are reported, not assumed.
type Json = null | boolean | number | string | Json[] | { [k: string]: Json }
const isKeyNode = (v: Json): v is { name: { value: number }; service: { value: number } } => {
  if (v === null || typeof v !== "object" || Array.isArray(v)) return false
  const keys = Object.keys(v)
  if (keys.length !== 2 || !keys.includes("name") || !keys.includes("service")) return false
  const name = (v as Record<string, Json>)["name"], service = (v as Record<string, Json>)["service"]
  const scalar = (x: Json) => x !== null && typeof x === "object" && !Array.isArray(x) &&
    Object.keys(x).length === 1 && typeof (x as Record<string, Json>)["value"] === "number"
  return scalar(name!) && scalar(service!)
}
const renumberKeys = (value: Json, seen: Map<number, number>, bases: number[]): Json => {
  if (Array.isArray(value)) return value.map(v => renumberKeys(v, seen, bases))
  if (value === null || typeof value !== "object") return value
  if (isKeyNode(value)) {
    const ordinal = value.name.value
    if (!seen.has(ordinal)) { if (seen.size === 0) bases.push(ordinal); seen.set(ordinal, seen.size) }
    return { name: { value: seen.get(ordinal)! }, service: { value: value.service.value } }
  }
  return Object.fromEntries(Object.entries(value as Record<string, Json>)
    .map(([k, v]) => [k, renumberKeys(v, seen, bases)]))
}
const upToKeyNumbering = (value: unknown, bases: number[]): string =>
  JSON.stringify(renumberKeys(value as Json, new Map(), bases))

/** A printed corpus file is one expression (`TypeScript.Render.expr`, `tools/Tools/Corpus.lean`).
 * The foreign contract reads modules, so the expression is wrapped in the module the truth
 * harness prints around the same expressions — the `effect` import header and one
 * `export const main`. Nothing else is added: the pure atoms are bare identifiers on both
 * contracts, and an opaque import (the truth harness's `../prelude.ts`) is `E-IMPORT-OPAQUE`
 * by design, which is why that harness's own modules are not this corpus. */
const asModule = (expression: string): string =>
  'import { Cause, Context, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope } from "effect"\n' +
  `export const main = ${expression.trimEnd()}\n`
const names = readdirSync(dir).filter(n => n.endsWith(".ts")).sort()
if (!names.length) throw new Error("empty required corpus")
if (mode === "inclusion-batch") {
  const report: Array<{ file: string; verdict: string }> = []
  for (const file of names.slice(Number(offset), Number(offset) + Number(count))) {
    const base = join(dir, file.slice(0, -3))
    const source = asModule(readFileSync(base + ".ts", "utf8"))
    const expected: unknown = JSON.parse(readFileSync(base + ".json", "utf8"))
    const left = ck.recognizeSource(source, file), right = oxc.recognizeSource(source, file)
    const one = (vs: ReadonlyArray<{ kind: string }>) => vs.length === 1 ? vs[0]! : undefined
    const l = one(left as never), r = one(right as never)
    if (l?.kind !== "lifted" || r?.kind !== "lifted") {
      const code = (v: unknown) => v === undefined ? "no-single-verdict"
        : (v as { kind: string; code?: string }).kind === "refusal" ? (v as { code?: string }).code ?? "refusal" : (v as { kind: string }).kind
      report.push({ file: basename(base), verdict: `refused ck=${code(l)} oxc=${code(r)}` })
      continue
    }
    if (compareVerdicts(left, right).status !== "agree") {
      throw new Error(`${basename(base)}: the two engines disagree on a printed module`)
    }
    const bases: number[] = []
    const oracle = upToKeyNumbering(expected, [])
    for (const [engine, v] of [["ck", l], ["oxc", r]] as const) {
      const lifted = upToKeyNumbering(effJson((v as unknown as { eff: never }).eff), bases)
      if (lifted !== oracle) {
        throw new Error(`${basename(base)}: ${engine} lifted a printed module to a different program up to key renumbering\n  oracle ${oracle}\n  lifted ${lifted}`)
      }
    }
    report.push({ file: basename(base), verdict: `included${bases.length ? ` (foreign key base ${bases[0]})` : ""}` })
  }
  process.stdout.write(report.map(r => `${r.file}\t${r.verdict}`).join("\n") + "\n")
} else if (mode === "printed-batch" || mode === "foreign-batch") {
  for (const file of names.slice(Number(offset), Number(offset) + Number(count))) {
    const base = join(dir, file.slice(0, -3)), source = readFileSync(base + ".ts", "utf8")
    const expected: unknown = JSON.parse(readFileSync(base + ".json", "utf8")), wire = readFileSync(base + ".eff").toString("hex")
    try {
      if (mode === "printed-batch") {
        for (const engine of [ck, oxc]) {
          const p = engine.readPrintedSource(source, file)
          if (!isDeepStrictEqual(effJson(p), expected) || Buffer.from(encodeProgram(p)).toString("hex") !== wire) throw new Error("printer oracle mismatch")
        }
      } else {
        const left = ck.recognizeSource(source, file), right = oxc.recognizeSource(source, file)
        const expectedKeys: unknown = JSON.parse(readFileSync(base + ".keys.json", "utf8"))
        if (compareVerdicts(left, right).status !== "agree") throw new Error(`engine disagreement: ${JSON.stringify({ left: left.map(v => v.kind === "refusal" ? v : { kind: v.kind, unit: v.unit, keys: v.keys }), right: right.map(v => v.kind === "refusal" ? v : { kind: v.kind, unit: v.unit, keys: v.keys }) })}`)
        if (left.length !== 1 || left[0]?.kind !== "lifted") throw new Error(`expected one lift: ${JSON.stringify(left)}`)
        for (const v of [left[0], right[0]]) {
          if (v?.kind !== "lifted" || !isDeepStrictEqual(effJson(v.eff), expected) || v.wireHex !== wire || !isDeepStrictEqual(v.keys, expectedKeys)) throw new Error(`foreign oracle mismatch: ${JSON.stringify(v)}`)
        }
      }
    } catch (e) { throw new Error(`${basename(base)}: ${String(e)}`, { cause: e }) }
  }
} else if (mode === "inclusion") {
  // DI-37: report the inclusion of the printed image in the foreign language over the corpus
  // that exists. A module the foreign contract admits and lifts to a *different* program is a
  // contradiction and fails; a module it refuses is counted and named by code, because the two
  // contracts are allowed to differ on the admitted language — that difference is the
  // measurement this mode exists to publish.
  const lines: string[] = []
  for (let at = 0; at < names.length; at += 500) {
    const run = spawnSync(process.execPath, [import.meta.filename, "inclusion-batch", dir, String(at), "500"], { encoding: "utf8", maxBuffer: 2 ** 24 })
    if (run.status !== 0) { process.stderr.write(run.stderr); throw new Error(`inclusion batch ${at} failed: ${run.status} ${run.error ?? ""}`) }
    lines.push(...run.stdout.trimEnd().split("\n").filter(Boolean))
  }
  const included = lines.filter(l => l.includes("\tincluded"))
  const refusals = new Map<string, number>()
  for (const line of lines) {
    if (line.includes("\tincluded")) continue
    const code = line.slice(line.indexOf("\t") + 1)
    refusals.set(code, (refusals.get(code) ?? 0) + 1)
  }
  const bases = new Set(included.filter(l => l.includes("(")).map(l => l.slice(l.indexOf("(") + 1, l.indexOf(")"))))
  const histogram = [...refusals].sort().map(([code, n]) => `${code} x${n}`).join(", ")
  console.log(`PASS inclusion: ${lines.length} printed modules, ${included.length} lifted by both engines to the printed oracle up to service-key renumbering${bases.size ? `; ${[...bases].join(", ")}` : ""}${refusals.size ? `; ${lines.length - included.length} refused by the foreign contract: ${histogram}` : "; no refusals"}`)
} else {
  if (mode !== "printed" && mode !== "foreign") throw new Error("unknown corpus mode")
  if (mode === "foreign") {
    const index = readFileSync(join(dir, "index.tsv"), "utf8").trimEnd().split("\n").slice(1)
    const indexed = index.map(r => r.split("\t")[0] + ".ts").sort()
    if (!isDeepStrictEqual(indexed, names)) throw new Error("foreign index differs from files")
    const counts = new Map<string, number>()
    for (const row of index) { const style = row.split("\t")[1]!; counts.set(style, (counts.get(style) ?? 0) + 1) }
    for (const row of readFileSync(join(dir, "counts.tsv"), "utf8").trimEnd().split("\n").slice(1)) {
      const [style, n] = row.split("\t")
      if (counts.get(style!) !== Number(n)) throw new Error(`style count mismatch: ${style}`)
    }
    if (counts.size !== 21 + 11520 || names.length !== 22986) throw new Error("foreign construction coverage/count changed")
  }
  for (let at = 0; at < names.length; at += 500) {
    const run = spawnSync(process.execPath, [import.meta.filename, mode + "-batch", dir, String(at), "500"], { encoding: "utf8", maxBuffer: 2 ** 24 })
    if (run.status !== 0) { process.stderr.write(run.stderr); throw new Error(`corpus batch ${at} failed: ${run.status} ${run.error ?? ""}`) }
  }
  console.log(`PASS ${mode}: ${names.length} exact JSON/wire comparisons on each independent reader${mode === "foreign" ? ", exact key tables and complete verdict agreement" : ""}; batch bound 500`)
}
