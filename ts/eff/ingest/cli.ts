import { recognize } from "./index.ts"
import { canonJson, encodeReport } from "./contract.ts"
import { checkRuntime } from "./pins.ts"
import { spawnSync } from "node:child_process"
import { fileURLToPath } from "node:url"
import { availableParallelism } from "node:os"
import { resolve } from "node:path"
const root = fileURLToPath(new URL("../../../", import.meta.url))
const args = process.argv.slice(2), verb = args.shift()
const option = (name: string, fallback: string): string => {
  const i = args.indexOf(name)
  if (i < 0) return fallback
  const v = args[i + 1]
  if (!v || v.startsWith("--")) throw new Error(`missing value for ${name}`)
  args.splice(i, 2); return v
}
const flag = (name: string) => { const i = args.indexOf(name); if (i < 0) return false; args.splice(i, 1); return true }
try {
  checkRuntime()
  if (!verb || verb === "--help" || verb === "help") {
    process.stdout.write("ingest recognize <paths...> [--engine ck|oxc|both] [--format jsonl|tsv] [--workers N] [--batch-size N] [--root PATH] [--cache PATH] [--force] [--bytes]\ningest gate --printed DIR --foreign DIR\ningest census <corpus>\ningest roundtrip <paths...>\n")
  } else if (verb === "recognize") {
    const engine = option("--engine", "both"), format = option("--format", "jsonl"), workers = Number(option("--workers", String(availableParallelism()))), batchSize = Number(option("--batch-size", "500")), from = option("--root", process.cwd()), cacheDir = option("--cache", ""), force = flag("--force")
    flag("--bytes") // wireHex is always present in lifted verdicts.
    if (!["ck", "oxc", "both"].includes(engine) || !["jsonl", "tsv"].includes(format) || !args.length || args.some(a => a.startsWith("--"))) throw new Error("invalid recognize arguments")
    let count = 0, red = false
    for await (const report of recognize(args, { engine: engine as "ck" | "oxc" | "both", root: from, workers, batchSize, ...(cacheDir ? { cacheDir } : {}), force })) {
      const encoded = canonJson(encodeReport(report))
      process.stdout.write(format === "jsonl" ? encoded + "\n" : `${report.file}\t${report.agreement}\t${encoded}\n`)
      red ||= report.agreement === "disagree"; count++
    }
    process.exitCode = count ? red ? 1 : 0 : 2
  } else if (verb === "gate") {
    const printed = resolve(option("--printed", ".lake/ingest-c3-printed")), foreign = resolve(option("--foreign", ".lake/ingest-c3-foreign"))
    if (args.length) throw new Error("unknown gate arguments")
    for (const [mode, path] of [["printed", printed], ["foreign", foreign]]) {
      const r = spawnSync(process.execPath, [fileURLToPath(new URL("./check-corpus.ts", import.meta.url)), mode!, path!], { stdio: "inherit", cwd: root })
      if (r.status !== 0) { process.exitCode = r.status === null ? 2 : 1; break }
    }
  } else if (verb === "census" || verb === "roundtrip") {
    // These verbs acquire their report drivers in commits 4 and 5 of the dispatch.
    throw new Error(`${verb} report driver has not landed; could not run`)
  } else throw new Error(`unknown verb: ${verb}`)
} catch (e) { process.stderr.write(`ingest: ${e instanceof Error ? e.message : String(e)}\n`); process.exitCode = 2 }
