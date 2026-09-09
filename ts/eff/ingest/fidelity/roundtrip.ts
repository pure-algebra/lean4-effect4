import { createHash } from "node:crypto"
import { createReadStream, existsSync, mkdirSync, readFileSync, writeFileSync, symlinkSync, realpathSync, rmSync } from "node:fs"
import { open, mkdir, copyFile } from "node:fs/promises"
import { createInterface } from "node:readline"
import { join, resolve, extname } from "node:path"
import { fileURLToPath } from "node:url"
import { spawnSync } from "node:child_process"
import { recognize, type Options } from "../index.ts"
import { canonJson } from "../contract.ts"
import { pinsDigest, checkRuntime } from "../pins.ts"
import { Generations, loadCorpus } from "../census/corpus.ts"
import { decodeInput, decodeObserved, decodePrinted, type Candidate, type InputFile, type Observed } from "./fidelity-contract.ts"
import { sourceModule } from "./source.ts"
const repo = fileURLToPath(new URL("../../../../", import.meta.url))
const fidelityPins = createHash("sha256").update(pinsDigest).update(Buffer.concat(["run-truth.ts", "prelude.ts", "IngestPrint.lean"].map(p => readFileSync(join(repo, "harness/truth", p))))).digest("hex")
export interface FidelityOptions extends Options { root: string; out: string; census?: never; censusFile?: string; timeoutMs?: number }
export function compareObserved(original: Observed, printed: Observed) {
  if (original.status !== "observed" || printed.status !== "observed") return { status: "could-not-run" as const, exitAgree: null, scheduleAgree: null }
  const a = original.observation, b = printed.observation
  // Same observation alphabet as run-truth.ts; only its existing scheduled rows are omitted.
  const schedule = (s: readonly string[]) => s.filter(r => !r.startsWith("scheduled "))
  const exitAgree = a.parked === b.parked && canonJson(a.exit) === canonJson(b.exit)
  const scheduleAgree = canonJson(schedule(a.schedule)) === canonJson(schedule(b.schedule))
  return { status: exitAgree && scheduleAgree ? "agree" as const : "disagree" as const, exitAgree, scheduleAgree }
}
async function* lines(path: string) { for await (const line of createInterface({ input: createReadStream(path), crlfDelay: Infinity })) if (line) yield line }
const printedHeader = `import { Cause, Context, Deferred, Effect, Exit, Fiber, Layer, Option, Ref, Scope } from "effect"\nimport { succ, pred, isZero, not, add, lt, eq, pair, fst, snd, incr, double, takeAndBump, zeroWhenPositive, noChange } from ${JSON.stringify(join(repo, "harness/truth/prelude.ts"))}\n`
export async function roundtrip(paths: readonly string[], options: FidelityOptions) {
  checkRuntime()
  const out = resolve(options.out), timeoutMs = options.timeoutMs ?? 300
  if (!Number.isInteger(timeoutMs) || timeoutMs < 1 || timeoutMs > 30000) throw new Error("invalid fidelity deadline")
  await mkdir(out, { recursive: true })
  const modules = join(repo, "ts/eff/node_modules"), link = join(out, "node_modules")
  if (!existsSync(link)) symlinkSync(modules, link, "dir")
  if (realpathSync(join(link, "effect")) !== realpathSync(join(modules, "effect"))) throw new Error("fidelity output selects another Effect installation")
  const roots = new Map<string, string>()
  if (options.censusFile) for (const p of loadCorpus(join(options.root, "experiments/parser-census/corpus-manifest.json"), join(options.root, "experiments/parser-census/project-labels.json"), options.root)) roots.set(p.id, resolve(options.root, p.localPath))
  else roots.set("input", resolve(options.root))
  const inputs = async function* (): AsyncGenerator<InputFile> {
    if (options.censusFile) { for await (const line of lines(options.censusFile)) yield decodeInput(JSON.parse(line)); return }
    const generations = new Generations(resolve(options.root))
    for await (const file of recognize(paths, { ...options, force: true })) yield decodeInput({ ...file, project: "input", generation: generations.forFile(file.file).generation })
  }
  const rows = await open(join(out, "fidelity.jsonl"), "w"), commands = await open(join(out, "commands.jsonl"), "w")
  const counts = { liftedUnits: 0, excludedV3: 0, excludedPreV3: 0, v4Units: 0, notAttemptedForeignImports: 0, notAttemptedRequirements: 0, notAttemptedIllTyped: 0, attempts: 0, agreements: 0, disagreements: 0, couldNotRun: 0, variantAttempts: 0 }
  let batch: Candidate[] = [], batchNumber = 0, id = 0
  const lane = join(repo, ".lake/LANE.lock"), owner = `ingest-fidelity-${process.pid}`
  let owned = false
  try { mkdirSync(lane); writeFileSync(join(lane, "owner"), owner + "\n"); owned = true }
  catch { if (!process.env.EFFECT4_LANE_OWNER || readFileSync(join(lane, "owner"), "utf8").trim() !== process.env.EFFECT4_LANE_OWNER) throw new Error("Lean lane held by another run") }
  const env = { ...process.env, LEAN_NUM_THREADS: "3", EFFECT4_LANE_OWNER: owned ? owner : process.env.EFFECT4_LANE_OWNER }
  const sourcePath = (file: InputFile) => {
    const root = roots.get(file.project)
    if (!root) throw new Error(`unknown source project: ${file.project}`)
    const path = resolve(root, file.file)
    if (!path.startsWith(root + "/")) throw new Error("source path escapes project")
    return path
  }
  const readSource = (file: InputFile) => {
    const source = readFileSync(sourcePath(file), "utf8")
    if (createHash("sha256").update(source).update(file.pins).digest("hex") !== file.contentDigest) throw new Error(`census source changed: ${file.project}/${file.file}`)
    return source
  }
  const writeRow = async (candidate: Candidate, result: unknown) => rows.write(canonJson({ pins: fidelityPins, censusPins: candidate.file.pins, project: candidate.file.project, file: candidate.file.file, unit: candidate.name, occurrence: candidate.occurrence, result }) + "\n")
  const observe = async (module: string, name: string, result: string): Promise<Observed> => {
    const command = ["bun", join(repo, "harness/truth/run-truth.ts"), "--observe", module, "--unit", name, "--result", result, "--timeout", String(timeoutMs)]
    rmSync(result, { force: true }) // A failed child must never reuse a previous observation.
    const run = spawnSync(command[0]!, command.slice(1), { cwd: out, env, encoding: "utf8", timeout: timeoutMs + 3000, maxBuffer: 4 * 1024 * 1024 })
    await commands.write(canonJson({ command, exit: run.status, signal: run.signal, error: run.error?.message ?? null }) + "\n")
    writeFileSync(result + ".log", run.stdout + run.stderr)
    if (!existsSync(result)) return { status: "could-not-run", error: run.error?.message ?? `module exited ${run.status}; ${run.signal ?? "no result"}` }
    return decodeObserved(JSON.parse(readFileSync(result, "utf8")))
  }
  const flush = async () => {
    if (!batch.length) return
    const dir = join(out, `batch-${batchNumber++}`); await mkdir(dir, { recursive: true })
    const hex = join(dir, "programs.hex"), rendered = join(dir, "printed.jsonl")
    writeFileSync(hex, [...new Set(batch.flatMap(c => c.variants.map(v => v.wireHex)))].join("\n") + "\n")
    const command = ["lake", "env", "lean", "-M4096", "--run", "harness/truth/IngestPrint.lean", hex, rendered]
    const run = spawnSync(command[0]!, command.slice(1), { cwd: repo, env, encoding: "utf8", timeout: 120000, maxBuffer: 8 * 1024 * 1024 })
    await commands.write(canonJson({ command, exit: run.status, signal: run.signal }) + "\n")
    writeFileSync(join(dir, "print.log"), run.stdout + run.stderr)
    if (run.status !== 0) throw new Error(`Lean print driver failed: ${run.stderr || run.stdout}`)
    const producerStamp = readFileSync(rendered + ".cut-from", "utf8").trim()
    if (!/^cut-from: .* inputs=[a-f0-9]{64}$/.test(producerStamp)) throw new Error("invalid Lean projection stamp")
    const printed = new Map<string, ReturnType<typeof decodePrinted>>()
    for await (const line of lines(rendered)) { const p = decodePrinted(JSON.parse(line)); printed.set(p.wireHex, p) }
    for (const candidate of batch) {
      const observations: unknown[] = [], statuses: string[] = []
      let requirements = false, illTyped = false
      const source = readSource(candidate.file), original = sourceModule(source, candidate.file.file)
      const unitDir = join(dir, String(id++)); await mkdir(unitDir, { recursive: true })
      await copyFile(sourcePath(candidate.file), join(unitDir, "source" + extname(candidate.file.file)))
      for (const [index, variant] of candidate.variants.entries()) {
        const p = printed.get(variant.wireHex)
        if (!p) throw new Error("missing Lean projection")
        if (!p.wellTyped) { illTyped = true; observations.push({ variant, status: "not-attempted", reason: "no inferred requirement row" }); continue }
        if (!p.requiresEmpty) { requirements = true; observations.push({ variant, status: "not-attempted", reason: "nonempty requirement row" }); continue }
        counts.variantAttempts++
        if (p.decl === null) { statuses.push("could-not-run"); observations.push({ variant, status: "could-not-run", reason: "Api.printDecl refused" }); continue }
        const printedFile = join(unitDir, `printed-${index}.ts`)
        writeFileSync(printedFile, printedHeader + p.decl)
        let host: Observed
        try {
          const selected = original.expose(candidate.name, candidate.occurrence, candidate.span), file = join(unitDir, `original-${index}${extname(candidate.file.file)}`)
          writeFileSync(file, selected.source)
          host = await observe(file, selected.name, join(unitDir, `original-${index}.json`))
        } catch (error) { host = { status: "could-not-run", error: String(error) } }
        const replay = await observe(printedFile, "main", join(unitDir, `printed-${index}.json`)), comparison = compareObserved(host, replay)
        statuses.push(comparison.status); observations.push({ variant, ...comparison, original: host, printed: replay })
      }
      if (!statuses.length) {
        if (requirements) counts.notAttemptedRequirements++; else if (illTyped) counts.notAttemptedIllTyped++
        await writeRow(candidate, { status: "not-attempted", producerStamp, observations }); continue
      }
      counts.attempts++
      const status = statuses.includes("disagree") ? "disagree" : statuses.includes("could-not-run") ? "could-not-run" : "agree"
      if (status === "agree") counts.agreements++
      else if (status === "disagree") counts.disagreements++
      else counts.couldNotRun++
      await writeRow(candidate, { status, producerStamp, fixture: unitDir.slice(out.length + 1), observations })
      if (counts.attempts % 50 === 0) process.stderr.write(`fidelity ${counts.agreements}/${counts.attempts}; ${counts.couldNotRun} could not run\n`)
    }
    batch = []
  }
  try {
    for await (const file of inputs()) {
      const units = new Map<string, Candidate>()
      for (const [engine, verdicts] of [["ck", file.ck], ["oxc", file.oxc]] as const) {
       const occurrences = new Map<string, number>()
       for (const v of verdicts ?? []) {
        const occurrence = occurrences.get(v.unit.name) ?? 0
        occurrences.set(v.unit.name, occurrence + 1)
        if (v.kind !== "lifted") continue
        const key = v.unit.name + "\0" + occurrence
        let unit = units.get(key)
        if (!unit) { unit = { file, name: v.unit.name, occurrence, span: v.unit.span, variants: [] }; units.set(key, unit) }
        const old = unit.variants.find(a => a.wireHex === v.wireHex && canonJson(a.keys) === canonJson(v.keys))
        if (old) old.engines.push(engine)
        else unit.variants.push({ wireHex: v.wireHex, keys: v.keys, engines: [engine] })
      }
      }
      counts.liftedUnits += units.size
      if (file.generation !== "v4") { if (file.generation === "v3") counts.excludedV3 += units.size; else counts.excludedPreV3 += units.size; continue }
      if (!units.size) continue
      counts.v4Units += units.size
      const source = sourceModule(readSource(file), file.file)
      for (const unit of units.values()) {
        if (source.foreign.length) { counts.notAttemptedForeignImports++; await writeRow(unit, { status: "not-attempted", foreignImports: source.foreign }); continue }
        batch.push(unit)
        if (batch.length === 500) await flush()
      }
    }
    await flush()
  } finally { await rows.close(); await commands.close(); if (owned) rmSync(lane, { recursive: true }) }
  const summary = { pins: fidelityPins, effect: "4.0.0-rc.112", timeoutMs, ...counts }
  writeFileSync(join(out, "summary.json"), canonJson(summary) + "\n")
  return summary
}
