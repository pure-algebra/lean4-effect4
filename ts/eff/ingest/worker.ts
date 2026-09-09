// One bounded worker batch; no AST or parser arena survives worker exit.
import { createHash } from "node:crypto"
import { parentPort } from "node:worker_threads"
import { readFileSync } from "node:fs"
import { Schema } from "effect"
import * as ck from "./ck.ts"
import * as oxc from "./oxc.ts"
import { compareVerdicts } from "./gate.ts"
import { pinsDigest, checkRuntime } from "./pins.ts"
import { compilerDeclarations, oxcDeclarations } from "./census/legs.ts"
import type { Decl, Metrics } from "./census/census-contract.ts"
import type { FileReport } from "./contract.ts"
const Job = Schema.Struct({ engine: Schema.Literals(["ck", "oxc", "both"]), census: Schema.optional(Schema.Boolean), files: Schema.Array(Schema.Struct({ path: Schema.String, name: Schema.String })) })
const decodeJob = Schema.decodeUnknownSync(Job)
const run = (input: unknown): { reports: FileReport[]; metrics: Metrics } => {
  checkRuntime()
  const job = decodeJob(input)
  if (job.files.length > 500) throw new Error("worker batch exceeds 500")
  const metrics = { files: job.files.length, bytes: 0, reads: 0, parseUs: 0, totalUs: 0 }
  const started = performance.now()
  const reports: FileReport[] = job.files.map(file => {
    const source = readFileSync(file.path, "utf8")
    metrics.reads++; metrics.bytes += Buffer.byteLength(source)
    let ckDeclarations: Decl[] | undefined, oxcDecls: readonly Decl[] | undefined
    let parseStart = performance.now()
    let ckParsed: boolean | null = null, oxcParsed: boolean | null = null
    const left = job.engine !== "oxc" ? ck.recognizeSource(source, file.name, ok => { ckParsed = ok; metrics.parseUs += Math.round((performance.now() - parseStart) * 1000) }, job.census ? tree => { ckDeclarations = compilerDeclarations(tree) } : undefined) : undefined
    parseStart = performance.now()
    const right = job.engine !== "ck" ? oxc.recognizeSource(source, file.name, ok => { oxcParsed = ok; metrics.parseUs += Math.round((performance.now() - parseStart) * 1000) }, job.census ? tree => { oxcDecls = oxcDeclarations(tree) } : undefined) : undefined
    const agreement = left && right ? compareVerdicts(left, right).status === "agree" && ckParsed === oxcParsed ? "agree" : "disagree" : "single"
    return { ...(ckDeclarations ? { ckDeclarations } : {}), ...(oxcDecls ? { oxcDeclarations: oxcDecls } : {}), file: file.name, pins: pinsDigest, contentDigest: createHash("sha256").update(source).update(pinsDigest).digest("hex"), ...(left ? { ck: left } : {}), ...(right ? { oxc: right } : {}), ckParsed, oxcParsed, agreement }
  })
  metrics.totalUs = Math.round((performance.now() - started) * 1000)
  return { reports, metrics }
}
if (parentPort) parentPort.once("message", input => { try { parentPort!.postMessage({ ok: true, ...run(input) }) } catch (e) { parentPort!.postMessage({ ok: false, error: String(e) }) } })
else self.onmessage = event => { try { self.postMessage({ ok: true, ...run(event.data) }) } catch (e) { self.postMessage({ ok: false, error: String(e) }) } }
