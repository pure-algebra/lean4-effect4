/**
 * Ledger transition-legality check (deferred M1 deliverable; lands with the
 * first status flip, per the plan's workflow-scaffolding rider).
 *
 * Compares the committed conformance ledger (HEAD) with the working copy
 * and asserts every per-obligation status moves along a legal edge: a
 * non-green status may stay, change wording, or become green; a green
 * status (instantiated, or discharged by carrier construction) never
 * changes — green never regresses. A declared model-version bump is the
 * only future escape hatch, and no bump mechanism exists yet, so any
 * green change fails. A FAMILY MISMATCH status in the working ledger
 * fails outright.
 */
import { execFileSync } from "node:child_process"
import { readFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const pkg = join(dirname(fileURLToPath(import.meta.url)), "..")
const ledgerRel = "library/effects/CONFORMANCE-LEDGER.md"

const statusRows = (text: string): Map<string, string> => {
  const rows = new Map<string, string>()
  for (const line of text.split(/\r?\n/)) {
    const m = /^\| (\S+) \| (.+) \|$/.exec(line)
    const id = m?.[1]
    const status = m?.[2]
    if (id !== undefined && status !== undefined && id !== "ID" && !/^-+$/.test(id)) {
      rows.set(id, status)
    }
  }
  return rows
}

let committed: string | null = null
try {
  committed = execFileSync("git", ["show", `HEAD:${ledgerRel}`], {
    cwd: pkg,
    encoding: "utf8",
  })
} catch {
  committed = null // no committed ledger yet; every row is new
}

const working = readFileSync(join(pkg, "CONFORMANCE-LEDGER.md"), "utf8")
const oldRows = committed === null ? new Map<string, string>() : statusRows(committed)
const newRows = statusRows(working)

const isGreen = (s: string) =>
  s.startsWith("instantiated") ||
  s.startsWith("discharged") ||
  s.startsWith("evidenced")
const errors: string[] = []
let flips = 0

for (const [id, status] of newRows) {
  if (status.startsWith("FAMILY MISMATCH")) {
    errors.push(`${id}: ${status}`)
  }
}
for (const [id, oldStatus] of oldRows) {
  if (!isGreen(oldStatus)) continue
  const newStatus = newRows.get(id)
  if (newStatus === undefined) {
    errors.push(`${id}: instantiated row removed — green never regresses`)
  } else if (newStatus !== oldStatus) {
    errors.push(
      `${id}: "${oldStatus}" -> "${newStatus}" — green never regresses without a declared model-version bump`,
    )
  }
}
for (const [id, status] of newRows) {
  if (isGreen(status) && !isGreen(oldRows.get(id) ?? "")) flips++
}

if (errors.length > 0) {
  for (const e of errors) console.error(`illegal ledger transition: ${e}`)
  process.exit(1)
}
console.log(
  `ledger transitions legal (${newRows.size} rows, ${flips} newly green)`,
)
