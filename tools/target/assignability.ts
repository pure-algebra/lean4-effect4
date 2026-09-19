#!/usr/bin/env bun
/**
 * The assignability differential (plan 1.10): `Ty.sub` against the one compiler's order.
 *
 *     bun tools/target/assignability.ts --repo . --vectors <ty-vectors.tsv> [--promote]
 *
 * `tools/Tools/TyVectors.lean` writes the questions — each pair as its two `Ty` values, the
 * strings `Ty.renderRaw` prints for them, `Ty.sub` in both directions, and the same two
 * verdicts under one swapped arm (the red control). This asks the compiler about the rendered
 * pair, both readings of both directions, and classifies every row:
 *
 *   agree       the order and the target say the same thing in both directions
 *   cut         they differ where this language deliberately does not distinguish what the
 *               target does, or the other way round; each cut is named by its reason
 *   incomplete  `Ty.sub` refuses a pair the target accepts: sound, not complete (§5.2)
 *   defect      `Ty.sub` accepts a pair the target refuses — the unsound direction
 *
 * A `defect` fails the lane. Anything else is recorded in `generated/assignability.tsv`, the
 * committed expected file: a fresh run that differs fails too, and `--promote` rewrites it.
 * The sensitivity of the control is printed, never committed — it is a property of this run,
 * not of the tree.
 */
import { readFileSync, writeFileSync } from "node:fs"
import { resolve } from "node:path"
import { assignability, type Pair, type PairObservation } from "./oracle.ts"

interface Vector { id: string; left: string; right: string; renderLeft: string; renderRight: string
  subLR: boolean; subRL: boolean; mutantLR: boolean; mutantRL: boolean }

const bool = (text: string, where: string): boolean => {
  if (text !== "true" && text !== "false") throw new Error(`${where}: expected a boolean, found ${JSON.stringify(text)}`)
  return text === "true"
}

export function readVectors(text: string): Vector[] {
  const vectors: Vector[] = []
  for (const line of text.split("\n")) {
    if (!line || line.startsWith("#")) continue
    const cells = line.split("\t")
    if (cells.length !== 9) throw new Error(`ty-vectors: expected 9 columns, found ${cells.length} in ${JSON.stringify(line)}`)
    const [id, left, right, renderLeft, renderRight, subLR, subRL, mutantLR, mutantRL] = cells as [string, string, string, string, string, string, string, string, string]
    vectors.push({ id, left, right, renderLeft, renderRight,
      subLR: bool(subLR, id), subRL: bool(subRL, id), mutantLR: bool(mutantLR, id), mutantRL: bool(mutantRL, id) })
  }
  if (!vectors.length) throw new Error("ty-vectors: no pairs")
  return vectors
}

/** The deliberate differences, each with the reason it is not a defect and not incompleteness.
 * A pair is a cut only when the reason applies to it; nothing is classified by its id. */
const cuts: Array<{ name: string; reason: string; holds: (v: Vector) => boolean }> = [
  { name: "cut/spelling", reason: "`Ty.renderRaw` is not injective (`nat` and `int` both print `number`; `refOf nat` prints the handle target `Ref.Ref<number>` a `.handle` prints verbatim), so the target cannot see a difference the order can",
    holds: v => v.renderLeft === v.renderRight && v.left !== v.right },
]

export type Verdict = "agree" | "cut" | "incomplete" | "defect"

export interface Row extends Vector {
  assignableLR: boolean | null; assignableRL: boolean | null
  statementLR: boolean | null; statementRL: boolean | null
  verdict: Verdict | "refused"; note: string
}

export function classify(vector: Vector, observation: PairObservation): Row {
  const assignableLR = observation.leftToRight.assignable, assignableRL = observation.rightToLeft.assignable
  const statementLR = observation.leftToRight.statement, statementRL = observation.rightToLeft.statement
  const base = { ...vector, assignableLR, assignableRL, statementLR, statementRL }
  if (observation.issues.length || statementLR === null || statementRL === null) {
    return { ...base, verdict: "refused", note: observation.issues.map(i => `${i.code}: ${i.message}`).join("; ") || "no verdict" }
  }
  const notes: string[] = []
  if (assignableLR !== statementLR || assignableRL !== statementRL) {
    notes.push("the checker's relation and the assignment statement disagree")
  }
  const agree = vector.subLR === statementLR && vector.subRL === statementRL
  if (agree) return { ...base, verdict: "agree", note: notes.join("; ") }
  const cut = cuts.find(c => c.holds(vector))
  if (cut) return { ...base, verdict: "cut", note: [cut.name + ": " + cut.reason, ...notes].join("; ") }
  const unsound = (vector.subLR && !statementLR) || (vector.subRL && !statementRL)
  if (unsound) return { ...base, verdict: "defect", note: ["the order accepts what the target refuses", ...notes].join("; ") }
  return { ...base, verdict: "incomplete", note: ["the order refuses what the target accepts", ...notes].join("; ") }
}

const COLUMNS = ["id", "renderLeft", "renderRight", "subLR", "subRL",
  "assignableLR", "assignableRL", "statementLR", "statementRL", "verdict", "note"] as const
const cell = (x: boolean | null) => x === null ? "-" : String(x)

export function render(rows: readonly Row[], version: string): string {
  return ["# GENERATED by make check-target (tools/target/assignability.ts over tools/Tools/TyVectors.lean's pairs); do not edit",
    `# compiler tsgo ${version}; \`Ty.sub\` against the target's order, both readings of both directions`,
    "# the three gaps of docs/research/2026-09-18-research-type-algebra.md §5.2: gap/option-union and",
    "# gap/prod-never are the first two rows; the third (function types are absent, so no contravariant",
    "# position exists) has no pair to witness it — there is no arrow to write on either side.",
    "# " + COLUMNS.join("\t"),
    ...rows.map(r => [r.id, r.renderLeft, r.renderRight, String(r.subLR), String(r.subRL),
      cell(r.assignableLR), cell(r.assignableRL), cell(r.statementLR), cell(r.statementRL), r.verdict, r.note].join("\t")),
    ""].join("\n")
}

if (import.meta.main) {
  const args = process.argv.slice(2)
  let repo = resolve(import.meta.dir, "../.."), vectors = "", promote = false
  for (let i = 0; i < args.length; i++) {
    const arg = args[i]
    if (arg === "--promote") { promote = true; continue }
    const value = args[++i]
    if (!value) throw new Error(`missing value for ${arg}`)
    if (arg === "--repo") repo = resolve(value)
    else if (arg === "--vectors") vectors = resolve(value)
    else throw new Error(`unknown option ${arg}`)
  }
  if (!vectors) throw new Error("--vectors is required")
  const expected = resolve(repo, "generated/assignability.tsv")
  const questions = readVectors(readFileSync(vectors, "utf8"))
  const report = assignability(repo, questions.map((v): Pair => ({ id: v.id, left: v.renderLeft, right: v.renderRight })))
  const byId = new Map(report.observations.map(o => [o.id, o]))
  const rows = questions.map(v => {
    const observation = byId.get(v.id)
    if (!observation) throw new Error(`the compiler answered nothing for ${v.id}`)
    return classify(v, observation)
  })
  const counts = new Map<string, number>()
  for (const row of rows) counts.set(row.verdict, (counts.get(row.verdict) ?? 0) + 1)
  // The control: the same pairs under one swapped `sub` arm. A pair catches the mutation when
  // the real order agrees with the target there and the mutant does not.
  const caught = rows.filter(r => r.statementLR !== null && r.statementRL !== null &&
    r.subLR === r.statementLR && r.subRL === r.statementRL &&
    (r.mutantLR !== r.statementLR || r.mutantRL !== r.statementRL))
  const moved = questions.filter(v => v.mutantLR !== v.subLR || v.mutantRL !== v.subRL)
  const text = render(rows, report.versions.typescript)
  console.log(`assignability: ${rows.length} pairs; ` +
    [...counts.entries()].sort().map(([k, n]) => `${k} ${n}`).join(", "))
  console.log(`assignability: red control (refOf covariant): ${moved.length} pair(s) move, ${caught.length} caught by the differential`)
  const defects = rows.filter(r => r.verdict === "defect")
  if (promote) {
    writeFileSync(expected, text)
    console.log(`assignability: wrote ${expected}`)
  } else {
    let committed: string | undefined
    try { committed = readFileSync(expected, "utf8") } catch { committed = undefined }
    if (committed !== text) {
      const fresh = resolve(repo, ".lake/target/assignability.tsv")
      writeFileSync(fresh, text)
      console.error(`FAIL assignability: generated/assignability.tsv differs from this run (see ${fresh}); promote it deliberately if the change is intended`)
      process.exit(1)
    }
  }
  if (!caught.length) {
    console.error("FAIL assignability: the red control is not caught by any pair; the differential measures nothing")
    process.exit(1)
  }
  if (defects.length) {
    console.error(`FAIL assignability: ${defects.length} pair(s) the order accepts and the target refuses: ${defects.map(d => d.id).join(", ")}`)
    process.exit(1)
  }
  console.log("PASS assignability: no pair the order accepts is refused by the target")
}
