// One bounded worker batch; no AST or parser arena survives worker exit.
import { createHash } from "node:crypto"
import { parentPort } from "node:worker_threads"
import { readFileSync } from "node:fs"
import { Schema } from "effect"
import * as ck from "./ck.ts"
import * as oxc from "./oxc.ts"
import { compareVerdicts } from "./gate.ts"
import { pinsDigest, checkRuntime } from "./pins.ts"
import type { FileReport } from "./contract.ts"
const Job = Schema.Struct({ engine: Schema.Literals(["ck", "oxc", "both"]), files: Schema.Array(Schema.Struct({ path: Schema.String, name: Schema.String })) })
const decodeJob = Schema.decodeUnknownSync(Job)
const run = (input: unknown): FileReport[] => {
  checkRuntime()
  const job = decodeJob(input)
  if (job.files.length > 500) throw new Error("worker batch exceeds 500")
  return job.files.map(file => {
    const source = readFileSync(file.path, "utf8")
    let ckParsed: boolean | null = null, oxcParsed: boolean | null = null
    const left = job.engine !== "oxc" ? ck.recognizeSource(source, file.name, ok => { ckParsed = ok }) : undefined
    const right = job.engine !== "ck" ? oxc.recognizeSource(source, file.name, ok => { oxcParsed = ok }) : undefined
    const agreement = left && right ? compareVerdicts(left, right).status === "agree" && ckParsed === oxcParsed ? "agree" : "disagree" : "single"
    return { file: file.name, pins: pinsDigest, contentDigest: createHash("sha256").update(source).update(pinsDigest).digest("hex"), ...(left ? { ck: left } : {}), ...(right ? { oxc: right } : {}), ckParsed, oxcParsed, agreement }
  })
}
if (parentPort) parentPort.once("message", input => { try { parentPort!.postMessage({ ok: true, reports: run(input) }) } catch (e) { parentPort!.postMessage({ ok: false, error: String(e) }) } })
else self.onmessage = event => { try { self.postMessage({ ok: true, reports: run(event.data) }) } catch (e) { self.postMessage({ ok: false, error: String(e) }) } }
