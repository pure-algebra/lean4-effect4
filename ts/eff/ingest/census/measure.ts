// Measure the same bounded recognition path; timing never enters verdict bytes.
import { createHash } from "node:crypto"
import { mkdirSync, writeFileSync, openSync, writeSync, closeSync } from "node:fs"
import { join, resolve } from "node:path"
import { availableParallelism } from "node:os"
import { recognize } from "../index.ts"
import { canonJson, encodeReport } from "../contract.ts"
import { loadCorpus, excluded } from "./corpus.ts"
import { checkRuntime, pinsDigest } from "../pins.ts"
checkRuntime()
const [root, out, engine, mode] = process.argv.slice(2)
if (!root || !out || !["ck", "oxc", "both"].includes(engine ?? "") || !["cold", "warm", "single"].includes(mode ?? "")) throw new Error("measure ROOT OUT ck|oxc|both cold|warm|single")
const projects = loadCorpus(join(root, "experiments/parser-census/corpus-manifest.json"), join(root, "experiments/parser-census/project-labels.json"), root)
mkdirSync(out, { recursive: true })
const runtime = process.versions.bun ? `bun-${process.versions.bun}` : `node-${process.versions.node}`
const name = `${runtime}-${engine}-${mode}`, workers = mode === "single" ? 1 : availableParallelism()
const fd = openSync(join(out, name + ".jsonl"), "w"), hash = createHash("sha256")
const metrics = { reads: 0, bytes: 0, parseUs: 0, totalUs: 0 }, start = performance.now()
let files = 0, pending = ""
try {
  for await (const r of recognize(projects.map(p => resolve(root, p.localPath)), { root, engine: engine as "ck" | "oxc" | "both", workers, batchSize: 500, cacheDir: join(out, "cache-" + engine), force: mode !== "warm", excludeDirs: excluded, onMetrics: m => { metrics.reads += m.reads; metrics.bytes += m.bytes; metrics.parseUs += m.parseUs; metrics.totalUs += m.totalUs } })) {
    const line = canonJson(encodeReport(r)) + "\n"
    hash.update(line); pending += line; files++
    if (pending.length >= 65536) { writeSync(fd, pending); pending = "" }
  }
  if (pending) writeSync(fd, pending)
} finally { closeSync(fd) }
const wallUs = Math.round((performance.now() - start) * 1000)
const result = { pins: pinsDigest, runtime, engine, mode, workers, batchSize: 500, files, ...metrics, wallUs, peakRssBytes: process.resourceUsage().maxRSS * (process.versions.bun && process.platform === "darwin" ? 1 : 1024), filesPerSecond: files / (wallUs / 1e6), megabytesPerSecond: metrics.bytes / wallUs, parseShare: metrics.totalUs ? metrics.parseUs / metrics.totalUs : 0, sha256: hash.digest("hex") }
writeFileSync(join(out, name + ".json"), JSON.stringify(result, null, 2) + "\n")
process.stdout.write(JSON.stringify(result) + "\n")
