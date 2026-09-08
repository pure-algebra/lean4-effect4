// Commit-2 construction check. Both parsers must accept every style, and every indexed
// source has its JSON and wire oracle. Exact foreign recognition is commit 3's gate.
// Parser children are recycled after 128 files to bound oxc's native arena lifetime.
import * as fs from "node:fs"
import * as path from "node:path"
import { spawnSync } from "node:child_process"
import * as ts from "typescript"
import { parseSync } from "oxc-parser"

const args = process.argv.slice(2)
if (args[0] === "--batch") {
  for (const file of args.slice(1)) {
    const source = fs.readFileSync(file, "utf8")
    const parsed = ts.createSourceFile(file, source, ts.ScriptTarget.Latest, false, ts.ScriptKind.TS)
    const diagnostics = (parsed as ts.SourceFile & { parseDiagnostics: readonly ts.Diagnostic[] }).parseDiagnostics
    const oxc = parseSync(file, source, { lang: "ts", sourceType: "module" })
    if (diagnostics.length || oxc.errors.length) {
      console.error(file, JSON.stringify({ tsc: diagnostics.map(d => ts.flattenDiagnosticMessageText(d.messageText, "\n")), oxc: oxc.errors }))
      process.exit(1)
    }
    const base = file.slice(0, -3)
    const json: unknown = JSON.parse(fs.readFileSync(base + ".json", "utf8"))
    const wire = fs.readFileSync(base + ".eff")
    if (!Array.isArray(json) || typeof json[0] !== "string" || wire.length < 18 || wire[0] !== 10) throw new Error(`missing or malformed oracle: ${file}`)
  }
} else {
  const dir = args[0]
  if (!dir) throw new Error("usage: bun run check-styles.ts <styles directory>")
  const rows = fs.readFileSync(path.join(dir, "index.tsv"), "utf8").trimEnd().split("\n").slice(1).map(r => r.split("\t"))
  const names = rows.map(r => r[0]!)
  if (!names.length || new Set(names).size !== names.length) throw new Error("empty or duplicate styles index")
  const files = names.map(name => path.join(dir, name + ".ts"))
  const actual = fs.readdirSync(dir).filter(n => n.endsWith(".ts")).sort()
  if (JSON.stringify(actual) !== JSON.stringify(names.map(n => n + ".ts").sort())) throw new Error("styles index does not enumerate all sources")
  const counts = new Map<string, number>()
  for (const row of rows) counts.set(row[1]!, (counts.get(row[1]!) ?? 0) + 1)
  const declared = fs.readFileSync(path.join(dir, "counts.tsv"), "utf8").trimEnd().split("\n").slice(1)
  if (declared.length !== counts.size) throw new Error("styles count table differs")
  for (const row of declared) {
    const [name, count] = row.split("\t")
    if (counts.get(name!) !== Number(count)) throw new Error(`style count differs: ${name}`)
  }
  const start = performance.now()
  for (let i = 0; i < files.length; i += 128) {
    const child = spawnSync(process.execPath, [import.meta.filename, "--batch", ...files.slice(i, i + 128)], { encoding: "utf8" })
    if (child.status !== 0) { console.error(child.stdout, child.stderr, child.error ?? ""); process.exit(1) }
  }
  console.log(`PASS styles construction: ${files.length} indexed files, ${counts.size} configurations, both parsers accept every source, JSON/wire oracle pairs present; parser children recycled at 128 files (${Math.round(performance.now() - start)} ms)`)
}
