// Commit-2 construction check. Both parsers must accept every style, and every indexed
// source has its JSON and wire oracle. Exact foreign recognition is commit 3's gate.
//
// The two parsers are the oracle's and oxc's. The oracle's grammar is tsgo 7's (decisions row 168,
// route (B)): the pinned preview's own API (`@typescript/native-preview/unstable/sync`) opens one
// project of every indexed source and reports each file's syntactic diagnostics. Its synchronous
// client reads node's pipe handle, which bun lacks, so that side runs as one node child (`--tsgo`);
// one compiler at one version, no second package. oxc's side runs in bun children recycled after
// 128 files to bound oxc's native arena lifetime.
import * as fs from "node:fs"
import * as path from "node:path"
import { spawnSync } from "node:child_process"
import { parseSync } from "oxc-parser"

const args = process.argv.slice(2)
const indexNames = (dir: string): string[] => fs.readFileSync(path.join(dir, "index.tsv"), "utf8").trimEnd().split("\n").slice(1).map(r => r.split("\t")[0]!)
const preview = JSON.parse(fs.readFileSync(new URL("./node_modules/@typescript/native-preview/package.json", import.meta.url), "utf8")) as { version: string }

if (args[0] === "--tsgo") {
  // Under node: one project whose configuration is served by the API's virtual file system (it is
  // written nowhere); every source falls back to the disk. Prints one JSON line per file that has
  // a syntactic diagnostic, then the count of files read.
  const dir = path.resolve(args[1]!)
  const { API } = await import("@typescript/native-preview/unstable/sync")
  const files = indexNames(dir).map(name => path.join(dir, name + ".ts"))
  const config = path.join(dir, "__check-styles.tsconfig.json")
  const settings = JSON.stringify({ files, compilerOptions: { target: "esnext", module: "esnext", noLib: true, noResolve: true, types: [] } })
  const api = new API({ cwd: dir, fs: { readFile: (f: string) => f === config ? settings : undefined, fileExists: (f: string) => f === config ? true : undefined } })
  try {
    const project = api.updateSnapshot({ openProjects: [config] }).getProject(config)
    if (!project) throw new Error("tsgo opened no project")
    const read = new Set(project.program.getSourceFileNames())
    const missing = files.filter(f => !read.has(f))
    if (missing.length) throw new Error(`tsgo did not read ${missing.length} sources, first ${missing[0]}`)
    const byFile = new Map<string, string[]>()
    for (const d of project.program.getSyntacticDiagnostics()) {
      const file = d.fileName ?? "<project>"
      byFile.set(file, [...byFile.get(file) ?? [], `TS${d.code} ${d.pos}-${d.end}: ${d.text}`])
    }
    for (const [file, messages] of byFile) console.log(JSON.stringify({ file, tsgo: messages }))
    console.log(JSON.stringify({ read: files.length }))
  } finally { api.close() }
} else if (args[0] === "--batch") {
  // Under bun: oxc's verdict and the oracle pair for each file; one JSON line per file oxc refuses.
  for (const file of args.slice(1)) {
    const source = fs.readFileSync(file, "utf8")
    const oxc = parseSync(file, source, { lang: "ts", sourceType: "module" })
    if (oxc.errors.length) console.log(JSON.stringify({ file, oxc: oxc.errors }))
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
  const refused = new Map<string, { tsgo?: unknown; oxc?: unknown }>()
  const node = process.env["NODE"] ?? "node"
  const oracle = spawnSync(node, ["--disable-warning=ExperimentalWarning", import.meta.filename, "--tsgo", dir], { encoding: "utf8", maxBuffer: 2 ** 28 })
  if (oracle.status !== 0) { console.error(oracle.stdout, oracle.stderr, oracle.error ?? ""); process.exit(1) }
  let read = -1
  for (const line of oracle.stdout.trimEnd().split("\n")) {
    const row = JSON.parse(line) as { file?: string; tsgo?: string[]; read?: number }
    if (row.read !== undefined) read = row.read
    else refused.set(row.file!, { tsgo: row.tsgo })
  }
  if (read !== files.length) throw new Error(`tsgo read ${read} of ${files.length} sources`)
  for (let i = 0; i < files.length; i += 128) {
    const child = spawnSync(process.execPath, [import.meta.filename, "--batch", ...files.slice(i, i + 128)], { encoding: "utf8", maxBuffer: 2 ** 26 })
    if (child.status !== 0) { console.error(child.stdout, child.stderr, child.error ?? ""); process.exit(1) }
    for (const line of child.stdout.trimEnd().split("\n").filter(Boolean)) {
      const row = JSON.parse(line) as { file: string; oxc: unknown }
      refused.set(row.file, { ...refused.get(row.file), oxc: row.oxc })
    }
  }
  if (refused.size) {
    for (const [file, verdict] of [...refused].slice(0, 20)) console.error(file, JSON.stringify(verdict))
    console.error(`FAIL styles construction: ${refused.size} sources refused by tsgo ${preview.version} or oxc`)
    process.exit(1)
  }
  console.log(`PASS styles construction: ${files.length} indexed files, ${counts.size} configurations, both parsers (tsgo ${preview.version} through its API, oxc) accept every source, JSON/wire oracle pairs present; oxc children recycled at 128 files (${Math.round(performance.now() - start)} ms)`)
}
