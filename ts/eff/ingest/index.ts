import { Worker as NodeWorker } from "node:worker_threads"
import { availableParallelism } from "node:os"
import { createHash } from "node:crypto"
import { pinsDigest } from "./pins.ts"
import { stat, readdir, readFile, writeFile, mkdir } from "node:fs/promises"
import { resolve, relative, join } from "node:path"
import { Schema } from "effect"
import { FileReport, type FileReport as Report } from "./contract.ts"
export { recognizeSource as recognizeCompilerSource } from "./ck.ts"
export { recognizeSource as recognizeOxcSource } from "./oxc.ts"
export type { Verdict, FileReport } from "./contract.ts"
const Reply = Schema.Union([Schema.Struct({ ok: Schema.Literal(true), reports: Schema.Array(FileReport) }), Schema.Struct({ ok: Schema.Literal(false), error: Schema.String })])
const decodeReply = Schema.decodeUnknownSync(Reply)
export interface Options { readonly engine?: "ck" | "oxc" | "both"; readonly root?: string; readonly workers?: number; readonly batchSize?: number; readonly cacheDir?: string; readonly force?: boolean }
async function* files(path: string): AsyncGenerator<string> {
  const s = await stat(path)
  if (s.isFile()) { if (/\.tsx?$/.test(path)) yield path; return }
  if (!s.isDirectory()) return
  const entries = await readdir(path, { withFileTypes: true })
  const key = (e: typeof entries[number]) => e.name + (e.isDirectory() ? "/" : "")
  entries.sort((a, b) => key(a) < key(b) ? -1 : key(a) > key(b) ? 1 : 0)
  for (const entry of entries) {
    if (["node_modules", ".git", ".lake"].includes(entry.name)) continue
    yield* files(join(path, entry.name))
  }
}
const runBatch = async (paths: readonly string[], root: string, engine: "ck" | "oxc" | "both", options: Options): Promise<readonly Report[]> => {
  const cached = new Map<string, Report>()
  const misses: string[] = []
  const locations = new Map<string, { cache: string; size: number; mtime: number }>()
  const Cache = Schema.Struct({ pins: Schema.String, size: Schema.Number, mtime: Schema.Number, report: FileReport })
  const decodeCache = Schema.decodeUnknownSync(Cache)
  if (options.cacheDir) await mkdir(options.cacheDir, { recursive: true })
  for (const path of paths) {
    if (!options.cacheDir) { misses.push(path); continue }
    const info = await stat(path), name = relative(root, path).replaceAll("\\", "/")
    const cache = join(options.cacheDir, createHash("sha256").update(path).update(root).update(engine).digest("hex") + ".json")
    locations.set(name, { cache, size: info.size, mtime: info.mtimeMs })
    if (!options.force) try {
      const entry = decodeCache(JSON.parse(await readFile(cache, "utf8")))
      if (entry.pins === pinsDigest && entry.size === info.size && entry.mtime === info.mtimeMs) { cached.set(name, entry.report); continue }
    } catch { /* Absent or invalid private cache is recomputed; gates use force. */ }
    misses.push(path)
  }
  if (!misses.length) return paths.map(path => cached.get(relative(root, path).replaceAll("\\", "/"))!)
  const job = { engine, files: misses.map(path => ({ path, name: relative(root, path).replaceAll("\\", "/") })) }
  const url = new URL("./worker.ts", import.meta.url)
  const value: unknown = await new Promise((resolve, reject) => {
    if (process.versions.bun) {
      const worker = new Worker(url.href)
      worker.onmessage = e => { worker.terminate(); resolve(e.data) }
      worker.onerror = e => { worker.terminate(); reject(new Error(e.message)) }
      worker.postMessage(job)
    } else {
      const worker = new NodeWorker(url, { execArgv: ["--experimental-transform-types", "--disable-warning=ExperimentalWarning"] })
      worker.once("message", value => { void worker.terminate(); resolve(value) })
      worker.once("error", reject)
      worker.once("exit", code => { if (code) reject(new Error(`worker exited ${code}`)) })
      worker.postMessage(job)
    }
  })
  const reply = decodeReply(value)
  if (!reply.ok) throw new Error(reply.error)
  for (const report of reply.reports) {
    cached.set(report.file, report)
    const loc = locations.get(report.file)
    if (loc) await writeFile(loc.cache, JSON.stringify({ pins: pinsDigest, size: loc.size, mtime: loc.mtime, report }) + "\n")
  }
  return paths.map(path => cached.get(relative(root, path).replaceAll("\\", "/"))!)
}
/** Files are sorted; only workers × batchSize reports may await ordered delivery. */
export async function* recognize(paths: readonly string[], options: Options = {}): AsyncGenerator<Report> {
  const batchSize = options.batchSize ?? 500, concurrency = options.workers ?? availableParallelism()
  if (!Number.isInteger(batchSize) || batchSize < 1 || batchSize > 500 || !Number.isInteger(concurrency) || concurrency < 1) throw new Error("invalid worker bounds")
  const root = resolve(options.root ?? process.cwd()), engine = options.engine ?? "both"
  const pending: Promise<readonly Report[]>[] = []
  let batch: string[] = []
  const roots = [...new Set(paths.map(p => resolve(p)))].sort()
  const iterators = roots.filter(p => !roots.some(other => other !== p && p.startsWith(other + "/"))).map(p => files(p))
  const next = await Promise.all(iterators.map(i => i.next()))
  while (next.some(n => !n.done)) {
    let selected = -1
    for (let i = 0; i < next.length; i++) {
      const n = next[i]!
      if (!n.done && (selected < 0 || n.value < next[selected]!.value!)) selected = i
    }
    const file = next[selected]!.value!
    next[selected] = await iterators[selected]!.next()
    {
      batch.push(file)
      if (batch.length !== batchSize) continue
      pending.push(runBatch(batch, root, engine, options)); batch = []
      if (pending.length >= concurrency) for (const report of await pending.shift()!) yield report
    }
  }
  if (batch.length) pending.push(runBatch(batch, root, engine, options))
  for (const batch of pending) for (const report of await batch) yield report
}
