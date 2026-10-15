// harness/tsdiag/run-tsdiag.mjs - the diagnostics lane: the printed corpus under the native
// TypeScript compiler, against this checker's located refusals (DI-86).
//
//   node harness/tsdiag/run-tsdiag.mjs <corpus dir> <work dir> [--promote]
//
// node, not bun: the compiler's synchronous client reads a node-internal pipe handle.
//
// Reads <corpus dir>/index.tsv (name, wellTyped, readable, chars, reason, path, codes: the
// checker's refusal and the codes predicted for it, Codegen/Diagnostics.lean), the programs'
// modules (<corpus dir>/modules), and the host configuration the corpus tool wrote
// (tsconfig.json, host-config.json). Writes each module under <work dir>/programs as it is, runs
// @typescript/native-preview's synchronous API once over the whole project, and records one row
// per program in generated/tsdiag-agreement.tsv.
//
// A module is the unchecked module of every lane's writer (tools/Drivers/Corpus.lean,
// `diagnosticsModule`; decisions row 392, P1 (a)): the program as `export const main = …` with no
// declared type, its imports from Lean data, laid out. So the compiler answers for the program on
// its own; whether it accepts Lean's declared type is the corpus lane's question, on the module
// that ships. This lane writes no byte of a module and keeps no list of names. Until 2026-10-15
// it wrote each program itself, under the imports of every name (harness/truth/module-imports.ts,
// deleted by decisions row 395 (3)).
// A module's header is what stands before its first `export`: its comment and its imports. The prelude stands beside the modules with every file that it
// reaches. The compiler names those files: the lane opens the tree's prelude as the one root
// of a project and copies each file of harness/truth that the compiler read. So a new file
// beside the prelude needs no edit here. Until 2026-10-06 the lane copied prelude.ts alone and
// wrote its imports by hand. The prelude's atoms had moved to a file beside it, so every
// program failed on its imports, and the lane measured nothing.
//
// A defect of the lane's own files is no fact about a program. The lane refuses to write a
// table when the project's options, a copied file of the prelude or the header of a module has
// a diagnostic. It names the diagnostic and stops. Its controls run on every run, before a
// table is compared or written: one clean project, and one defective project for each kind of
// defect, which the lane must refuse by its reason. One kind removes a file of the prelude, and
// it has one project for each file.
//
// The verdicts:
//
//   typed-clean      this checker types it, TypeScript reports nothing
//   typed-errors     this checker types it, TypeScript refuses it: the lane FAILS
//   refused-agree    both refuse; the observed codes meet the predicted ones
//   refused-other    both refuse; no predicted code was observed (the table has a gap)
//   refused-unmapped both refuse; the reason has no predicted codes yet
//   refused-silent   this checker refuses, TypeScript accepts, as the table predicts (a
//                    restriction of the machine, the error alphabet)
//   refused-gap      this checker refuses with predicted codes, TypeScript accepts
//
// File-level codes of the module system and the advisory always-truthy codes are recorded in
// their own column and never decide a verdict. Without --promote the rows must equal the
// committed table; with it the table is rewritten. The compiler's version must equal the pin.
import fs from "node:fs"
import path from "node:path"

const [corpusDir, workDir, ...flags] = process.argv.slice(2)
if (!corpusDir || !workDir) throw new Error("run-tsdiag.mjs <corpus dir> <work dir> [--promote]")
const promote = flags.includes("--promote")
const repo = process.cwd()
// One compiler, one install (decisions row 57): the pinned `@typescript/native-preview` of
// ts/eff/package.json, the same one the target oracle and both typechecks run.
const home = process.env.TSGO_HOME ?? path.join(repo, "ts/eff/node_modules/@typescript/native-preview")
const committed = path.join(repo, "generated", "tsdiag-agreement.tsv")

// ---- pins ---------------------------------------------------------------------------
const hostConfig = JSON.parse(fs.readFileSync(path.join(corpusDir, "host-config.json"), "utf8"))
if (!fs.existsSync(path.join(home, "package.json")))
  throw new Error(`tsdiag: @typescript/native-preview not found at ${home} (bun install in ts/eff, or set TSGO_HOME)`)
const version = JSON.parse(fs.readFileSync(path.join(home, "package.json"), "utf8")).version
if (version !== hostConfig.version)
  throw new Error(`tsdiag: pin drift: @typescript/native-preview ${version}, HostConfig.pinned says ${hostConfig.version}`)
const effectVersion = JSON.parse(fs.readFileSync(path.join(repo, "ts/eff/node_modules/effect/package.json"), "utf8")).version
if (effectVersion !== hostConfig.effectVersion)
  throw new Error(`tsdiag: pin drift: effect ${effectVersion}, HostConfig.pinned says ${hostConfig.effectVersion}`)
const { API } = await import(path.join(home, "dist/api/sync/api.js"))

// ---- the index -------------------------------------------------------------------------
const index = new Map()
for (const line of fs.readFileSync(path.join(corpusDir, "index.tsv"), "utf8").split("\n")) {
  if (!line || line.startsWith("#")) continue
  const [name, wellTyped, , , reason, blamePath, codes] = line.split("\t")
  index.set(name, { wellTyped: wellTyped === "true", reason, blamePath,
    predicted: codes === "-" ? [] : codes.split("|").map(Number) })
}

// ---- the prelude's files ---------------------------------------------------------------
// The compiler names them. The tree's prelude is the one root of a project under the corpus's
// options, and every file of harness/truth that the compiler read is a file of the prelude.
// A file of the tree outside harness/truth has no place beside the modules: the lane refuses it.
const truth = fs.realpathSync(path.join(repo, "harness/truth"))
const tree = fs.realpathSync(repo)
const corpusConfig = fs.readFileSync(path.join(corpusDir, "tsconfig.json"), "utf8")
fs.rmSync(workDir, { recursive: true, force: true })
const closureConfig = path.join(workDir, "prelude-closure", "tsconfig.json")
fs.mkdirSync(path.dirname(closureConfig), { recursive: true })
fs.writeFileSync(closureConfig, JSON.stringify(
  { compilerOptions: JSON.parse(corpusConfig).compilerOptions, files: [path.join(truth, "prelude.ts")] }, null, 2) + "\n")
const closureApi = new API({ cwd: path.dirname(closureConfig) })
const reached = closureApi.updateSnapshot({ openProjects: [closureConfig] }).getProjects()[0].program.getSourceFileNames()
closureApi.close()
const inside = (dir, file) => { const rel = path.relative(dir, file); return rel !== "" && !rel.startsWith("..") && !path.isAbsolute(rel) }
const inPackage = (file) => file.split(/[\\/]/).includes("node_modules")
const preludeFiles = []
for (const name of reached) {
  if (inPackage(name) || !fs.existsSync(name)) continue  // a package, or a library of the compiler
  const file = fs.realpathSync(name)
  if (inside(truth, file)) preludeFiles.push(path.relative(truth, file))
  else if (inside(tree, file) && !inPackage(path.relative(tree, file)))
    throw new Error(`tsdiag: the prelude reaches ${path.relative(tree, file)}, outside harness/truth; the lane copies the prelude's folder only`)
}
preludeFiles.sort()
if (!preludeFiles.includes("prelude.ts")) throw new Error("tsdiag: the compiler did not read harness/truth/prelude.ts")

// ---- one project, one native run -------------------------------------------------------
const fileLevel = new Set([1287, 1295, 1479])
const advisory = new Set([2872, 2873])

/** Where a module's header ends: the start of its first line that begins `export`. */
const headerLength = (text) => {
  const at = text.search(/^export /m)
  if (at < 0) throw new Error("tsdiag: a module declares nothing")
  return at
}

/** The project of `modules` (a program's name to its module's text) in `dir`, under one native
 * run: each module is written as it is. The prelude's files stand beside the modules, and
 * `config` is the project's tsconfig text. `header` changes a module's header, and `spoil` the
 * built folder, before the run: only a control passes either. Returns each program's codes, the
 * diagnostics as rows, and the defects of the lane's own files, each with its count: a
 * diagnostic of the project's options, of a file of the prelude, or of a module's header. */
function measure(dir, modules, { header = (text) => text, config = corpusConfig, spoil = () => {} } = {}) {
  fs.mkdirSync(path.join(dir, "programs"), { recursive: true })
  for (const rel of preludeFiles) {
    fs.mkdirSync(path.dirname(path.join(dir, rel)), { recursive: true })
    fs.copyFileSync(path.join(truth, rel), path.join(dir, rel))
  }
  const headers = new Map()
  for (const [name, text] of modules) {
    const written = header(text)
    headers.set(name, headerLength(written))
    fs.writeFileSync(path.join(dir, "programs", `${name}.ts`), written)
  }
  fs.writeFileSync(path.join(dir, "tsconfig.json"), config)
  fs.symlinkSync(path.join(repo, "ts/eff/node_modules"), path.join(dir, "node_modules"))
  spoil(dir)
  const api = new API({ cwd: dir })
  const program = api.updateSnapshot({ openProjects: [path.join(dir, "tsconfig.json")] }).getProjects()[0].program
  const said = (d) => `TS${d.code} ${d.text.replace(/\s+/g, " ")}`
  const defects = new Map()
  const defect = (line) => defects.set(line, (defects.get(line) ?? 0) + 1)
  // The compiler gives one option's diagnostic in more than one of its three lists.
  new Set([...program.getConfigFileParsingDiagnostics(), ...program.getProgramDiagnostics(), ...program.getGlobalDiagnostics()]
    .map((d) => `the project: ${said(d)}`)).forEach(defect)
  for (const rel of preludeFiles) {
    const file = path.join(dir, rel)
    if (!fs.existsSync(file)) continue  // a control removed it: its importer reports the loss
    for (const d of [...program.getSyntacticDiagnostics(file), ...program.getSemanticDiagnostics(file)]) defect(`${rel}: ${said(d)}`)
  }
  const diagnostics = []
  const observed = new Map()
  for (const name of modules.keys()) {
    const file = path.join(dir, "programs", `${name}.ts`)
    const codes = { errors: new Set(), side: new Set() }
    for (const d of [...program.getSyntacticDiagnostics(file), ...program.getSemanticDiagnostics(file)]) {
      diagnostics.push([name, d.pos, d.end, d.code, d.text.replace(/\s+/g, " ")].join("\t"))
      if (fileLevel.has(d.code) || advisory.has(d.code)) codes.side.add(d.code)
      // A diagnostic that starts in a module's header is the header's: its imports are what the
      // writer read off the module, and no program's fact.
      else if (d.pos < headers.get(name)) defect(`the header of a module: ${said(d)}`)
      else codes.errors.add(d.code)
    }
    observed.set(name, codes)
  }
  api.close()
  return { defects, observed, diagnostics }
}

// ---- the corpus ------------------------------------------------------------------------
/** A program's module, as the corpus tool wrote it (tools/Drivers/Corpus.lean). */
const moduleOf = (file) => {
  const text = fs.readFileSync(file, "utf8")
  if (!/^[\x00-\x7f]*$/.test(text)) throw new Error(`tsdiag: ${file} is not ASCII`)
  return text
}
const modules = new Map()
for (const name of index.keys()) modules.set(name, moduleOf(path.join(corpusDir, "modules", `${name}.ts`)))
const started = performance.now()
const { defects, observed, diagnostics } = measure(workDir, modules)
const elapsed = ((performance.now() - started) / 1000).toFixed(2)
fs.writeFileSync(path.join(workDir, "diagnostics.tsv"), "# name\tpos\tend\tcode\ttext\n" + diagnostics.join("\n") + "\n")
if (defects.size > 0) {
  console.error(`FAIL check-tsdiag: the lane's own files do not check, so no program was measured and no table is written (see ${path.join(workDir, "diagnostics.tsv")}):`)
  for (const [line, count] of defects) console.error(`  ${line}${count > 1 ? ` (${count} times)` : ""}`)
  process.exit(1)
}

// ---- the controls, before any table ----------------------------------------------------
// The corpus's project has no defect here. The controls say that the lane would have seen one.
// Two programs, written by the corpus tool's writer as every module is
// (<corpus dir>/modules/controls): `succ` on a number checks, and `succ` on a Boolean is refused
// with 2345. The clean project must show exactly that and no defect. Each defective project must
// be refused with a defect of the kind that was put in.
const controlBodies = new Map(["checks", "refused"].map((name) =>
  [name, moduleOf(path.join(corpusDir, "modules", "controls", `${name}.ts`))]))
const controlFailures = []
let controls = 0
const control = (name, changes, holds) => {
  controls += 1
  const got = measure(path.join(workDir, "controls", String(controls)), controlBodies, changes)
  const why = holds(got)
  if (why) controlFailures.push(`${name}: ${why}; the lane reported ${JSON.stringify([...got.defects.keys()])}`)
}
const refusedBy = (prefix) => ({ defects }) =>
  [...defects.keys()].some((line) => line.startsWith(prefix)) ? null : `no defect starts with "${prefix}"`
control("the clean project", {}, ({ defects, observed }) =>
  defects.size > 0 ? "a defect was reported"
    : observed.get("checks").errors.size > 0 ? `the program that checks has the codes ${[...observed.get("checks").errors]}`
    : !observed.get("refused").errors.has(2345) ? `the refused program has the codes ${[...observed.get("refused").errors]}, not 2345`
    : null)
control("a header that names what the prelude does not export",
  { header: (text) => text.slice(0, headerLength(text)) + 'import { notAnExportOfThePrelude } from "../prelude.ts"\n' +
      text.slice(headerLength(text)) },
  refusedBy("the header of a module: TS2305"))
// The defect that this lane had until 2026-10-06, for each file in turn: the prelude without
// a file that it reaches.
for (const rel of preludeFiles.filter((file) => file !== "prelude.ts"))
  control(`the prelude without ${rel}`, { spoil: (dir) => fs.rmSync(path.join(dir, rel)) },
    ({ defects }) => [...defects.keys()].some((line) => line.includes(": TS2307 ")) ? null : "no defect is TS2307 (a module that is not found)")
control("a file of the prelude that does not check",
  { spoil: (dir) => fs.appendFileSync(path.join(dir, "prelude.ts"), '\nexport const controlDefect: number = "no number"\n') },
  refusedBy("prelude.ts: TS2322"))
control("an option that the compiler does not know",
  { config: JSON.stringify({ ...JSON.parse(corpusConfig), compilerOptions: { ...JSON.parse(corpusConfig).compilerOptions, notAnOptionOfTheCompiler: true } }) },
  refusedBy("the project: TS5023"))
if (controlFailures.length > 0) {
  console.error(`FAIL check-tsdiag: ${controlFailures.length} of the lane's ${controls} controls did not hold, so no table is compared or written:`)
  for (const line of controlFailures) console.error(`  ${line}`)
  process.exit(1)
}
console.log(`tsdiag: ${controls} controls hold: the clean project, and ${controls - 1} defective projects refused by their reasons (the prelude has ${preludeFiles.length} files)`)

// ---- the verdicts ----------------------------------------------------------------------
const rows = []
const counts = new Map()
for (const [name, entry] of [...index.entries()].sort((a, b) => a[0].localeCompare(b[0]))) {
  const { errors, side } = observed.get(name)
  const hit = entry.predicted.filter((c) => errors.has(c))
  let verdict
  if (entry.wellTyped) verdict = errors.size === 0 ? "typed-clean" : "typed-errors"
  else if (errors.size > 0) verdict = entry.predicted.length === 0 ? "refused-unmapped" : hit.length > 0 ? "refused-agree" : "refused-other"
  else verdict = entry.predicted.length === 0 ? "refused-silent" : "refused-gap"
  counts.set(verdict, (counts.get(verdict) ?? 0) + 1)
  const list = (s) => s.size === 0 ? "-" : [...s].sort((a, b) => a - b).join("|")
  rows.push([name, entry.wellTyped, entry.reason, entry.blamePath,
    entry.predicted.length === 0 ? "-" : entry.predicted.join("|"), list(errors), list(side), verdict].join("\t"))
}
const table = [
  "# GENERATED by make gen-tsdiag (harness/tsdiag/run-tsdiag.mjs over the printed corpus under Codegen/Diagnostics.lean's pinned host configuration); do not edit",
  `# compiler ${hostConfig.compiler} ${hostConfig.version}, effect ${hostConfig.effectVersion}`,
  "# name\twellTyped\treason\tpath\tpredicted\tobserved\tside\tverdict",
  ...rows, ""].join("\n")
const summary = [...counts.entries()].sort().map(([k, n]) => `${k} ${n}`).join(", ")
console.log(`tsdiag: ${index.size} programs, one native run in ${elapsed}s: ${summary}`)

if (promote) {
  fs.writeFileSync(committed, table)
  console.log(`tsdiag: wrote ${path.relative(repo, committed)}`)
} else if (!fs.existsSync(committed) || fs.readFileSync(committed, "utf8") !== table) {
  fs.writeFileSync(path.join(workDir, "tsdiag-agreement.tsv"), table)
  console.error(`FAIL check-tsdiag: ${path.relative(repo, committed)} differs from this run (see ${path.join(workDir, "tsdiag-agreement.tsv")}); promote with make gen-tsdiag if the change is intended`)
  process.exit(1)
}
if ((counts.get("typed-errors") ?? 0) > 0) {
  console.error(`FAIL check-tsdiag: ${counts.get("typed-errors")} program(s) this checker types are refused by TypeScript`)
  process.exit(1)
}
console.log("PASS check-tsdiag: no program this checker types is refused by TypeScript; the agreement table is what this run observed")
