// Real recorder/Lean-print smoke test, including a poisoned rerun of the same output path.
import { Schema } from "effect"
import { spawnSync } from "node:child_process"
import { mkdtempSync, cpSync, readFileSync, writeFileSync, rmSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"
import { fileURLToPath } from "node:url"
const repo = fileURLToPath(new URL("../../../", import.meta.url))
const work = mkdtempSync(join(tmpdir(), "effect4-fidelity-test-")), input = join(work, "input"), out = join(work, "out")
const Summary = Schema.Struct({ attempts: Schema.Number, agreements: Schema.Number, disagreements: Schema.Number, couldNotRun: Schema.Number, excludedV3: Schema.Number, notAttemptedRequirements: Schema.Number, notAttemptedForeignImports: Schema.Number })
const decode = Schema.decodeUnknownSync(Summary)
const run = () => {
  const result = spawnSync("bun", [join(repo, "ts/eff/ingest/cli.ts"), "roundtrip", input, "--root", input, "--out", out, "--workers", "1"], { cwd: repo, encoding: "utf8", timeout: 120000 })
  if (result.error) throw result.error
  const summary = decode(JSON.parse(readFileSync(join(out, "summary.json"), "utf8")))
  return { result, summary }
}
try {
  cpSync(join(repo, "ts/eff/ingest/fixtures/fidelity"), input, { recursive: true })
  const first = run(), a = first.summary
  if (first.result.status !== 0 || a.attempts !== 4 || a.agreements !== 4 || a.disagreements || a.couldNotRun || a.excludedV3 !== 1 || a.notAttemptedRequirements !== 1 || a.notAttemptedForeignImports !== 1) throw new Error(`fidelity fixture failed: ${JSON.stringify(first)}`)
  const source = join(input, "values.ts")
  writeFileSync(source, 'throw new Error("poisoned original module");\n' + readFileSync(source, "utf8"))
  const second = run(), b = second.summary
  if (second.result.status !== 2 || b.attempts !== 4 || b.agreements !== 0 || b.couldNotRun !== 4) throw new Error(`stale observation accepted: ${JSON.stringify(second)}`)
  process.stdout.write("PASS fidelity: four original/reprinted programs agree; requirement, foreign import and v3 exclusions hold; poisoned rerun reuses no old observations\n")
} finally { rmSync(work, { recursive: true, force: true }) }
