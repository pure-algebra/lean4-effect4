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
    process.stdout.write("ingest recognize <paths...> [--engine ck|oxc|both] [--format jsonl|tsv] [--workers N] [--batch-size N] [--root PATH] [--cache PATH] [--force] [--bytes]\ningest census [--root FOLDLAB] [--out DIR] [--force]\n")
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
  } else if (verb === "census") {
    const root = resolve(option("--root", "/Users/pooks/Dev/foldlab")), manifest = option("--manifest", root + "/experiments/parser-census/corpus-manifest.json"), labels = option("--labels", root + "/experiments/parser-census/project-labels.json"), out = resolve(option("--out", ".lake/ingest-census")), workers = Number(option("--workers", String(availableParallelism()))), batchSize = Number(option("--batch-size", "500")), engine = option("--engine", "both"), cacheDir = option("--cache", ""), force = flag("--force")
    if (args.length || !["ck", "oxc", "both"].includes(engine)) throw new Error("invalid census arguments")
    const { census } = await import("./census/capture.ts")
    const summary = await census({ root, manifest, labels, out, workers, batchSize, engine: engine as "ck" | "oxc" | "both", ...(cacheDir ? { cacheDir } : {}), force })
    process.stdout.write(canonJson(summary) + "\n")
    process.exitCode = summary.disagreeFiles ? 1 : 0
  } else throw new Error(`unknown verb: ${verb}`)
} catch (e) { process.stderr.write(`ingest: ${e instanceof Error ? e.message : String(e)}\n`); process.exitCode = 2 }
