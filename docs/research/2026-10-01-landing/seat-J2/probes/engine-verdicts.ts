// Seat J2, step 1: one engine's verdicts over every corpus the ingest lane reads, one canonical JSON
// line per file, so that two engines (or one engine before and after an edit) are compared file by
// file rather than by counts. The engine is loaded by dynamic import: run with `oxc` at the base, it
// never loads `ck.ts`, so `typescript@5.9.2` is never run (the owner's rule).
//
//   bun engine-verdicts.ts <ck|oxc> <printed|inclusion|foreign|fixtures|meta-printed|meta-recognize> <dir> <out.jsonl>
//
// The modes mirror `ts/eff/ingest/check-corpus.ts` (printed, inclusion, foreign) and
// `check-metamorphic.ts` (the six source edits, per engine); `fixtures` records the verdicts of every
// `.ts` under a directory. Batches of 500 files run in child processes, as the lane's own checks do,
// to bound oxc's native arena.
import { readFileSync, readdirSync, writeFileSync } from "node:fs"
import { spawnSync } from "node:child_process"
import { join, basename } from "node:path"
import { isDeepStrictEqual } from "node:util"

const ingest = new URL("../../../../../ts/eff/ingest/", import.meta.url)
const [engineName, mode, dir, out, offset = "0", count = "500"] = process.argv.slice(2)
if (!engineName || !["ck", "oxc"].includes(engineName) || !mode || !dir) throw new Error("usage: engine-verdicts.ts <ck|oxc> <mode> <dir> <out.jsonl>")
const names = readdirSync(dir).filter(n => n.endsWith(".ts")).sort()

if (mode.endsWith("-batch")) {
  const engine = await import(new URL(`./${engineName}.ts`, ingest).href)
  const { canonJson, verdictKey, sourceEditKey } = await import(new URL("./contract.ts", ingest).href)
  const { effJson } = await import(new URL("../json.gen.ts", ingest).href)
  const { encodeProgram } = await import(new URL("../wire.gen.ts", ingest).href)
  const kind = mode.slice(0, -"-batch".length)
  const asModule = (expression: string): string =>
    'import { Cause, Context, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope } from "effect"\n' +
    `export const main = ${expression.trimEnd()}\n`
  type Json = null | boolean | number | string | Json[] | { [k: string]: Json }
  const renumber = (value: Json, seen: Map<number, number>): Json => {
    if (Array.isArray(value)) return value.map(v => renumber(v, seen))
    if (value === null || typeof value !== "object") return value
    const keys = Object.keys(value)
    const scalar = (x: Json | undefined) => x !== null && typeof x === "object" && !Array.isArray(x) && Object.keys(x).length === 1 && typeof (x as Record<string, Json>)["value"] === "number"
    if (keys.length === 2 && scalar(value["name"]) && scalar(value["service"])) {
      const ordinal = ((value["name"] as Record<string, Json>)["value"]) as number
      if (!seen.has(ordinal)) seen.set(ordinal, seen.size)
      return { name: { value: seen.get(ordinal)! }, service: value["service"]! }
    }
    return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, renumber(v, seen)]))
  }
  const variants = (source: string): string[] => {
    const extras = 'import { Context as UnusedContext } from "effect";\nconst __unusedKey = UnusedContext.Service<number>("unused");\nconst __unused = 7;\n'
    return ["// comment\n" + source, source.replace(/;\r?\n/g, ";  \n\n"), source.replace(/\r?\n/g, "\r\n"),
      source.replace(/startImmediately: (true|false), uninterruptible: (true|false|"inherit")/g, "uninterruptible: $2, startImmediately: $1"),
      extras + source, source + "\n" + extras]
  }
  const attempt = <A>(f: () => A): { ok: true; value: A } | { ok: false; error: string } => {
    try { return { ok: true, value: f() } } catch (e) { return { ok: false, error: e instanceof Error ? e.message : String(e) } }
  }
  const lines: string[] = []
  for (const file of names.slice(Number(offset), Number(offset) + Number(count))) {
    const base = join(dir, file.slice(0, -3)), source = readFileSync(base + ".ts", "utf8")
    const row: Record<string, unknown> = { file: basename(base) }
    if (kind === "printed") {
      const expected: unknown = JSON.parse(readFileSync(base + ".json", "utf8")), wire = readFileSync(base + ".eff").toString("hex")
      const r = attempt(() => engine.readPrintedSource(source, file))
      if (r.ok) { row.json = canonJson(effJson(r.value)); row.oracle = isDeepStrictEqual(effJson(r.value), expected) && Buffer.from(encodeProgram(r.value)).toString("hex") === wire }
      else { row.error = r.error; row.oracle = false }
    } else if (kind === "inclusion") {
      const expected = JSON.parse(readFileSync(base + ".json", "utf8")) as Json
      let parsed: boolean | null = null
      const vs = engine.recognizeSource(asModule(source), file, (ok: boolean) => { parsed = ok })
      row.parsed = parsed; row.verdicts = vs.map((v: unknown) => canonJson(verdictKey(v)))
      const v = vs.length === 1 ? vs[0] : undefined
      row.class = !v ? `count ${vs.length}` : v.kind === "refusal" ? `refused ${v.code}`
        : JSON.stringify(renumber(effJson(v.eff) as Json, new Map())) === JSON.stringify(renumber(expected, new Map())) ? "included" : "mismatch"
    } else if (kind === "foreign" || kind === "fixtures") {
      let parsed: boolean | null = null
      const vs = engine.recognizeSource(source, file, (ok: boolean) => { parsed = ok })
      row.parsed = parsed; row.verdicts = vs.map((v: unknown) => canonJson(verdictKey(v)))
      if (kind === "foreign") {
        const expected: unknown = JSON.parse(readFileSync(base + ".json", "utf8")), wire = readFileSync(base + ".eff").toString("hex")
        const keys: unknown = JSON.parse(readFileSync(base + ".keys.json", "utf8"))
        const v = vs[0]
        row.oracle = vs.length === 1 && v?.kind === "lifted" && isDeepStrictEqual(effJson(v.eff), expected) && v.wireHex === wire && isDeepStrictEqual(v.keys, keys)
      }
    } else if (kind === "meta-printed") {
      const r = attempt(() => canonJson(effJson(engine.readPrintedSource(source, file))))
      row.stable = r.ok && variants(source).every(s => { const a = attempt(() => canonJson(effJson(engine.readPrintedSource(s, file)))); return a.ok && a.value === r.value })
    } else if (kind === "meta-recognize") {
      const before = engine.recognizeSource(source, file)
      const drift: string[] = []
      variants(source).forEach((s, i) => {
        const after = engine.recognizeSource(s, file)
        for (const expected of before) {
          const actual = after.find((v: { unit: { name: string } }) => v.unit.name === expected.unit.name)
          if (!actual || canonJson(sourceEditKey(actual)) !== canonJson(sourceEditKey(expected))) drift.push(`${i}:${expected.unit.name}`)
        }
      })
      row.units = before.length; row.drift = drift
    } else throw new Error(`unknown mode ${kind}`)
    lines.push(JSON.stringify(row))
  }
  process.stdout.write(lines.join("\n") + (lines.length ? "\n" : ""))
} else {
  if (!out) throw new Error("missing output path")
  const lines: string[] = []
  for (let at = 0; at < names.length; at += 500) {
    const run = spawnSync(process.execPath, [import.meta.filename, engineName, `${mode}-batch`, dir, "-", String(at), "500"], { encoding: "utf8", maxBuffer: 2 ** 28 })
    if (run.status !== 0) { process.stderr.write(run.stderr); throw new Error(`batch ${at} failed: ${run.status} ${run.error ?? ""}`) }
    lines.push(...run.stdout.split("\n").filter(Boolean))
  }
  writeFileSync(out, lines.join("\n") + "\n")
  const rows = lines.map(l => JSON.parse(l) as Record<string, unknown>)
  const tally = (key: string) => { const m = new Map<string, number>(); for (const r of rows) { const k = String(r[key]); m.set(k, (m.get(k) ?? 0) + 1) } return [...m].sort().map(([k, n]) => `${k} x${n}`).join(", ") }
  const summary = mode === "printed" ? `oracle: ${tally("oracle")}`
    : mode === "inclusion" ? `parsed: ${tally("parsed")}; class: ${tally("class")}`
    : mode === "foreign" ? `parsed: ${tally("parsed")}; oracle: ${tally("oracle")}; verdicts: ${rows.reduce((n, r) => n + (r.verdicts as unknown[]).length, 0)}`
    : mode === "fixtures" ? `parsed: ${tally("parsed")}; verdicts: ${rows.reduce((n, r) => n + (r.verdicts as unknown[]).length, 0)}`
    : mode === "meta-printed" ? `stable: ${tally("stable")}`
    : `units: ${rows.reduce((n, r) => n + (r.units as number), 0)}; files with drift: ${rows.filter(r => (r.drift as unknown[]).length).length}`
  console.log(`${engineName} ${mode} ${dir}: ${rows.length} files; ${summary}`)
}
