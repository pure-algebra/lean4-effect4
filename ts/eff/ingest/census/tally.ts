// Retargeted from foldlab experiments/parser-census/src/tally.ts at 4005d34f.
// Scores count I3 ingestion units. Declaration enumeration is a separate observation.
import { canonJson, verdictKey, type FileReport, type Verdict } from "../contract.ts"
import type { Bucket, Generation } from "./census-contract.ts"
export const bucket = (): Bucket => ({ candidates: 0, lifted: 0, refused: 0, disagree: 0, codes: {}, heads: {} })
const increment = (counts: Record<string, number>, key: string) => { counts[key] = (counts[key] ?? 0) + 1 }
export function pairs(report: FileReport): readonly { left: Verdict | null; right: Verdict | null }[] {
  const right = [...report.oxc ?? []]
  const rows = (report.ck ?? []).map(left => {
    const i = right.findIndex(v => v.unit.name === left.unit.name)
    return { left, right: i < 0 ? null : right.splice(i, 1)[0]! }
  })
  return [...rows, ...right.map(right => ({ left: null, right }))]
}
export const headSpelling = (v: Verdict | null) => v?.kind === "refusal" && v.code === "E-OP-UNKNOWN" ? v.detail.replace(/^unknown head: /, "") : null
export const equal = (left: Verdict | null, right: Verdict | null) => !!left && !!right && canonJson(verdictKey(left)) === canonJson(verdictKey(right))
export function add(bucket: Bucket, left: Verdict | null, right: Verdict | null): void {
  bucket.candidates++
  if (!equal(left, right)) bucket.disagree++
  // A recognized unit has a corroborated lift. Single-engine lifts remain visible, not agreements.
  if (equal(left, right) && left?.kind === "lifted") bucket.lifted++
  else {
    bucket.refused++
    const codes = new Set([left, right].filter(v => v?.kind === "refusal").map(v => v!.code))
    for (const code of codes) { if (code === "E-HELPER-UNPINNED") throw new Error("reserved refusal emitted"); increment(bucket.codes, code) }
    for (const head of new Set([headSpelling(left), headSpelling(right)].filter(h => h !== null))) increment(bucket.heads, head)
  }
}
export const ordered = (counts: Record<string, number>) => Object.entries(counts).sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]))
export const strata = (): Record<Generation, Bucket> => ({ v4: bucket(), v3: bucket(), "pre-v3": bucket() })
