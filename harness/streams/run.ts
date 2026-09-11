/** Execute pinned examples with each documented expectation turned into an exact assertion.
 * Each example has a separate process and a deadline; timeouts and missing observations fail.
 * The census, source hash and runner hash are retained with each observation receipt. */
import { instrument } from "./instrument.ts"
import { createHash } from "node:crypto"
import { mkdir, readFile, readdir, writeFile } from "node:fs/promises"
import { resolve } from "node:path"

interface Row {
  id: string; module: string; source: string; sourceLines: [number, number]
  spanDigest: string; program: string; expected: string[]; layer: number; leanStatus: string
}
interface Receipt { id: string; stamp: string; status: string; checks: number; detail?: string }
const root = resolve(import.meta.dir, "../..")
const args = process.argv.slice(2)
const arg = (name: string, fallback: string) => {
  const index = args.indexOf(name)
  return index < 0 ? fallback : args[index + 1] ?? fallback
}
const selected = arg("--modules", "Stream,Channel,Pull,Queue,Scope,Sink,PubSub,Fiber").split(",")
const output = resolve(arg("--out", resolve(import.meta.dir, "result.json")))
const work = resolve(arg("--work", resolve(import.meta.dir, ".work")))
const limit = Number(arg("--jobs", "6")), deadline = Number(arg("--timeout", "8000"))
const hash = (s: string) => createHash("sha256").update(s).digest("hex")
const census = JSON.parse(await readFile(resolve(import.meta.dir, "census.json"), "utf8")) as { rows: Row[] }
const rows = census.rows.filter(row => selected.includes(row.module))
if (rows.length === 0 || !Number.isInteger(limit) || limit < 1) throw Error("empty selection or invalid jobs")
await mkdir(work, { recursive: true })
const runnerHash = hash((await readFile(import.meta.path, "utf8")) + await readFile(resolve(import.meta.dir, "instrument.ts"), "utf8"))
const pinFiles = (await readdir(resolve(root, "vendor/effect-4.0.0-rc.112/src"), { recursive: true }))
  .filter(path => path.endsWith(".ts")).sort()
const pinHasher = createHash("sha256")
for (const path of pinFiles) {
  pinHasher.update(path + "\0")
  pinHasher.update(await readFile(resolve(root, "vendor/effect-4.0.0-rc.112/src", path)))
}
const pinHash = pinHasher.digest("hex")
const typeHasher = createHash("sha256")
const typePackage = resolve(root, "ts/eff/node_modules/effect")
const packageText = await readFile(resolve(typePackage, "package.json"), "utf8")
if (JSON.parse(packageText).version !== "4.0.0-rc.112") throw Error("type examples require effect@4.0.0-rc.112")
typeHasher.update(packageText)
typeHasher.update(await readFile(resolve(root, "ts/eff/node_modules/typescript/lib/typescript.js")))
for (const path of (await readdir(resolve(typePackage, "dist"), { recursive: true })).filter(path => path.endsWith(".d.ts")).sort()) {
  typeHasher.update(path + "\0")
  typeHasher.update(await readFile(resolve(typePackage, "dist", path)))
}
const typeHash = typeHasher.digest("hex")
const censusCheck = Bun.spawn(["python3", resolve(root, "scripts/generate-effect-stream-census.py"), "--check"], { stdout: "ignore", stderr: "inherit" })
if (await censusCheck.exited !== 0) throw Error("census drift")
// These pinned examples supply no output oracle. Keep them out of exact-output counts.
const typeOnly = new Set(["Stream-003", "Stream-004"])
const executionOnly = new Set(Array.from({ length: 8 }, (_, i) => `Fiber-${String(i + 7).padStart(3, "0")}`))
const sourceHashes = new Map<string, string>()
for (const row of rows) {
  if (!sourceHashes.has(row.source)) sourceHashes.set(row.source, hash(await readFile(resolve(root, row.source), "utf8")))
}
let cache: Receipt[] = []
if (!args.includes("--force")) {
  try { cache = (JSON.parse(await readFile(output, "utf8")) as { rows: Receipt[] }).rows } catch {}
}


let cursor = 0
const receipts: Receipt[] = new Array(rows.length)
async function worker() {
  while (cursor < rows.length) {
    const index = cursor++, row = rows[index]!
    const stamp = hash([runnerHash, pinHash, typeHash, sourceHashes.get(row.source), row.spanDigest, Bun.version, deadline].join("\n"))
    const previous = cache.find(r => r.id === row.id && r.stamp === stamp && ["passed", "typechecked", "executed"].includes(r.status))
    if (previous) { receipts[index] = previous; continue }
    try {
      const noOracle = typeOnly.has(row.id) || executionOnly.has(row.id)
      if (noOracle && row.expected.length !== 0) throw Error("no-oracle census changed")
      const instrumented = instrument(row, noOracle)
      if (typeOnly.has(row.id)) {
        const typePath = resolve(work, row.id + ".types.ts")
        await writeFile(typePath, row.program.replace('from "effect"', 'from ' + JSON.stringify(resolve(root, "ts/eff/node_modules/effect/dist/index.js"))))
        const checker = Bun.spawn([process.execPath, resolve(root, "ts/eff/node_modules/typescript/bin/tsc"),
          "--noEmit", "--strict", "--skipLibCheck", "--module", "ESNext", "--moduleResolution", "bundler", "--target", "ES2022", typePath],
          { stdout: "pipe", stderr: "pipe" })
        const [status, stdout, stderr] = await Promise.all([checker.exited, new Response(checker.stdout).text(), new Response(checker.stderr).text()])
        receipts[index] = { id: row.id, stamp, status: status === 0 ? "typechecked" : "failed", checks: 0,
          ...(status === 0 ? {} : { detail: (stdout + stderr).slice(-4000) }) }
        continue
      }
      const path = resolve(work, row.id + ".ts")
      await writeFile(path, instrumented.code)
      const child = Bun.spawn([process.execPath, path], { cwd: root, stdout: "pipe", stderr: "pipe" })
      let timedOut = false
      const timer = setTimeout(() => { timedOut = true; child.kill() }, deadline)
      const [exitCode, stdout, stderr] = await Promise.all([
        child.exited, new Response(child.stdout).text(), new Response(child.stderr).text()
      ])
      clearTimeout(timer)
      receipts[index] = { id: row.id, stamp, status: timedOut ? "timeout" : exitCode === 0 ? noOracle ? "executed" : "passed" : "failed",
        checks: instrumented.checks, ...(exitCode === 0 ? {} : { detail: (stderr || stdout).slice(-4000) }) }
    } catch (error) {
      receipts[index] = { id: row.id, stamp, status: "unsupported", checks: 0, detail: String(error) }
    }
  }
}
await Promise.all(Array.from({ length: limit }, worker))
const counts = Object.fromEntries(selected.map(module => [module, {
  total: rows.filter(row => row.module === module).length,
  passed: rows.filter((row, i) => row.module === module && receipts[i]?.status === "passed").length,
  typechecked: rows.filter((row, i) => row.module === module && receipts[i]?.status === "typechecked").length,
  executedWithoutOracle: rows.filter((row, i) => row.module === module && receipts[i]?.status === "executed").length
}]))
await writeFile(output, JSON.stringify({ format: "effect4-stream-observations-v1", pin: "4.0.0-rc.112",
  runtime: Bun.version, runnerHash, pinHash, typeHash, counts, rows: receipts }, null, 2) + "\n")
console.log(JSON.stringify({ counts, failures: receipts.filter(row => !["passed", "typechecked", "executed"].includes(row.status)).map(row => [row.id, row.status]) }))
process.exitCode = receipts.every(row => ["passed", "typechecked", "executed"].includes(row.status)) ? 0 : 1
