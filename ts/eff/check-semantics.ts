// bun run check-semantics.ts <report.json>; refuses shape, links, and excess keys.
import { readFileSync } from "node:fs"
import { decodeSemanticsReport } from "./semantics.ts"

const args = process.argv.slice(2)
if (args.length !== 1) {
  console.error("usage: bun run check-semantics.ts <report.json>")
  process.exit(2)
}
const file = args[0]!
let raw = ""
try {
  raw = readFileSync(file, "utf8")
  const input: unknown = JSON.parse(raw)
  const report = decodeSemanticsReport(input)
  console.log(`PASS semantics report: ${report.concepts.length} concepts, ${report.claims.length} claims`)
} catch (error) {
  console.error(`${file}: ${String(error)}`)
  if (raw.length > 0) console.error(`input head: ${raw.slice(0, 256)}`)
  process.exit(1)
}
