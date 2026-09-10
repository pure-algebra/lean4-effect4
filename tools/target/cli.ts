#!/usr/bin/env bun
import { mkdirSync, readFileSync, writeFileSync } from "node:fs"
import { dirname, resolve } from "node:path"
import { repositoryReport } from "./profile.ts"
import { query } from "./oracle.ts"
import { decodeQueries } from "./input.ts"

const args = process.argv.slice(2)
let repo = resolve(import.meta.dir, "../.."), output = ".lake/target/report.json", input: string | undefined
try {
  for (let i = 0; i < args.length; i++) {
    const arg = args[i], value = args[++i]
    if (!value) throw new Error(`missing value for ${arg}`)
    if (arg === "--repo") repo = resolve(value)
    else if (arg === "--out") output = value
    else if (arg === "--queries") input = value
    else throw new Error(`unknown option ${arg}`)
  }
  const report = input === undefined ? repositoryReport(repo) : query(repo, decodeQueries(JSON.parse(readFileSync(resolve(repo, input), "utf8"))), "explicit-query-selection")
  const file = resolve(repo, output)
  mkdirSync(dirname(file), { recursive: true })
  writeFileSync(file, JSON.stringify(report, null, 2) + "\n")
  console.log(`target conformance [${report.profile}]: ${report.conforms ? "PASS" : "FAIL"}; ${report.expected.length} expected, ${report.attempted.length} attempted, ${report.resolved.length} resolved, ${report.mismatching.length} mismatching, ${report.refused.length} refused`)
  for (const observation of report.observations.filter(o => o.status !== "agree")) console.log(`${observation.status}: ${observation.id}; ${observation.issues.map(i => i.code).join(",") || Object.entries(observation.columns).filter(([, c]) => c.actualToExpected === false || c.expectedToActual === false).map(([axis]) => axis).join(",")}`)
  console.log(`report: ${file}`)
  process.exitCode = report.conforms ? 0 : 1
} catch (error) {
  console.error(`target conformance: REFUSED input: ${String(error)}`)
  process.exitCode = 2
}
