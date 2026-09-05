// The corpus check: every `.ts` in the given directories is read, and where a `.json` of the
// same name exists (beside it, or in the `--oracle` directory) the reader's JSON must be
// byte-identical to it. Files without an oracle are reported as accepted or refused.
//
//   bun run check.ts <dir> [<dir>…] [--oracle <dir>]
//
// The oracle files are written by `src/Tools/ImageCorpus.lean`: the program Lean's own
// reader gets back after the printer (`Api.roundTrip`). A match is this reader agreeing with
// Lean's reader on that program. Exit status 1 on any mismatch or any refusal of a program
// that has an oracle.

import * as fs from "node:fs"
import * as path from "node:path"
import { Result } from "effect"
import { toJson } from "./json.gen.ts"
import { readTypeScript, showRefusal } from "./read.ts"

const args = process.argv.slice(2)
const dirs: string[] = []
let oracleDir: string | undefined
for (let i = 0; i < args.length; i++) {
  const a = args[i]!
  if (a === "--oracle") oracleDir = args[++i]
  else dirs.push(a)
}
if (dirs.length === 0) {
  console.error("usage: bun run check.ts <dir> [<dir>…] [--oracle <dir>]")
  process.exit(2)
}

let files = 0
let matched = 0
let mismatched = 0
let refusedWithOracle = 0
let acceptedNoOracle = 0
let refusedNoOracle = 0
const problems: string[] = []
const refusalKinds = new Map<string, number>()
const started = performance.now()

for (const dir of dirs) {
  for (const name of fs.readdirSync(dir).sort()) {
    if (!name.endsWith(".ts")) continue
    files++
    const file = path.join(dir, name)
    const base = name.slice(0, -3)
    const beside = path.join(dir, `${base}.json`)
    const inOracle = oracleDir ? path.join(oracleDir, `${base}.json`) : undefined
    const oracle = fs.existsSync(beside) ? beside : inOracle && fs.existsSync(inOracle) ? inOracle : undefined
    const result = readTypeScript(fs.readFileSync(file, "utf8"), name)
    if (Result.isFailure(result)) {
      const shown = showRefusal(result.failure)
      refusalKinds.set(result.failure._tag, (refusalKinds.get(result.failure._tag) ?? 0) + 1)
      if (oracle) {
        refusedWithOracle++
        problems.push(`${file}: refused: ${shown}`)
      } else {
        refusedNoOracle++
        problems.push(`${file}: refused (no oracle): ${shown}`)
      }
      continue
    }
    if (!oracle) {
      acceptedNoOracle++
      continue
    }
    const expected = fs.readFileSync(oracle, "utf8").trimEnd()
    const actual = toJson(result.success)
    if (actual === expected) matched++
    else {
      mismatched++
      const at = [...actual].findIndex((c, i) => c !== expected[i])
      problems.push(`${file}: JSON differs from ${oracle} at byte ${at}:\n    got  ${actual.slice(Math.max(0, at - 40), at + 60)}\n    want ${expected.slice(Math.max(0, at - 40), at + 60)}`)
    }
  }
}

const ms = Math.round(performance.now() - started)
console.log(`files ${files}: matched ${matched}, mismatched ${mismatched}, refused with oracle ${refusedWithOracle}, accepted without oracle ${acceptedNoOracle}, refused without oracle ${refusedNoOracle} (${ms} ms)`)
if (refusalKinds.size > 0) console.log(`refusals by kind: ${[...refusalKinds.entries()].map(([k, c]) => `${k} ${c}`).join(", ")}`)
for (const p of problems.slice(0, 20)) console.log(`  ${p}`)
if (problems.length > 20) console.log(`  … ${problems.length - 20} more`)
process.exit(mismatched + refusedWithOracle > 0 ? 1 : 0)
