#!/usr/bin/env bun
/**
 * Seat R, question 3: row 68's assignability differential over the record pairs, on a copy of
 * the vectors (`record-vectors.tsv`, written by `probes/Q3PrintedTypes.lean`), in this folder.
 *
 *     bun run.ts
 *
 * The lane's own driver (`tools/target/assignability.ts` through `tools/target/checker.ts`)
 * drives tsgo's API from the repository's `ts/eff/node_modules`, which this worktree does not
 * have; this copy asks the pinned CLI instead (`/opt/homebrew/bin/tsgo`, 7.0.0-dev.20260629.1,
 * the version `generated/assignability.tsv` records) and reads one of the lane's two readings,
 * the assignment statement (`oracle.ts` `pairSource`, both directions). The other reading, the
 * checker's `isTypeAssignableTo`, is not taken here and is reported as `-`. Verdicts follow
 * `classify` (`tools/target/assignability.ts:68-85`): agree, cut (spelling), incomplete, defect.
 */
import { mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { join } from "node:path"

const here = import.meta.dir
const tsgo = "/opt/homebrew/bin/tsgo"
const assignmentCodes = new Set([2322, 2375, 2739, 2740, 2741])

interface Vector { id: string; left: string; right: string; renderLeft: string; renderRight: string
  subLR: boolean; subRL: boolean; mutantLR: boolean; mutantRL: boolean }

const vectors: Vector[] = readFileSync(join(here, "record-vectors.tsv"), "utf8").split("\n")
  .filter(l => l && !l.startsWith("#")).map(l => {
    const c = l.split("\t")
    if (c.length !== 9) throw new Error(`expected 9 columns: ${l}`)
    const b = (t: string) => { if (t !== "true" && t !== "false") throw new Error(t); return t === "true" }
    return { id: c[0]!, left: c[1]!, right: c[2]!, renderLeft: c[3]!, renderRight: c[4]!,
      subLR: b(c[5]!), subRL: b(c[6]!), mutantLR: b(c[7]!), mutantRL: b(c[8]!) }
  })

const dir = join(here, "pairs")
rmSync(dir, { recursive: true, force: true })
mkdirSync(dir)
vectors.forEach((v, i) => writeFileSync(join(dir, `p${i}.ts`), [
  'import type { Option } from "effect"',
  `type __Left = ${v.renderLeft}`,
  `type __Right = ${v.renderRight}`,
  "declare const __left: __Left",
  "declare const __right: __Right",
  "export const __pair_leftToRight: __Right = __left",
  "export const __pair_rightToLeft: __Left = __right",
  "export type __Use = Option.Option<never>", ""].join("\n")))
writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({
  extends: "../../names/tsconfig.base.json", include: vectors.map((_, i) => `p${i}.ts`) }, null, 2))

const version = new TextDecoder().decode(Bun.spawnSync([tsgo, "--version"]).stdout).trim()
const run = Bun.spawnSync([tsgo, "-p", join(dir, "tsconfig.json"), "--pretty", "false"], { cwd: dir })
const out = new TextDecoder().decode(run.stdout) + new TextDecoder().decode(run.stderr)
const diags = out.split("\n").map(l => /^(?:.*[\\/])?p(\d+)\.ts\((\d+),\d+\): error TS(\d+): (.*)$/.exec(l))
  .filter((m): m is RegExpExecArray => m !== null)
  .map(m => ({ pair: Number(m[1]), line: Number(m[2]), code: Number(m[3]), text: m[4]! }))

const rows = vectors.map((v, i) => {
  const mine = diags.filter(d => d.pair === i)
  const other = mine.filter(d => !(assignmentCodes.has(d.code) && (d.line === 6 || d.line === 7)))
  if (other.length) return { v, lr: null, rl: null, verdict: "refused", note: other.map(d => `TS${d.code}: ${d.text}`).join("; ") }
  const lr = !mine.some(d => d.line === 6), rl = !mine.some(d => d.line === 7)
  let verdict: string, note = ""
  if (v.subLR === lr && v.subRL === rl) verdict = "agree"
  else if (v.renderLeft === v.renderRight && v.left !== v.right) { verdict = "cut"; note = "cut/spelling" }
  else if ((v.subLR && !lr) || (v.subRL && !rl)) { verdict = "defect"; note = "the order accepts what the target refuses" }
  else { verdict = "incomplete"; note = "the order refuses what the target accepts" }
  return { v, lr, rl, verdict, note }
})
const cell = (x: boolean | null) => x === null ? "-" : String(x)
const text = [`# seat R: record pairs, tsgo ${version} (${tsgo}), statement reading only (isTypeAssignableTo not run: '-')`,
  "# id\trenderLeft\trenderRight\tsubLR\tsubRL\tassignableLR\tassignableRL\tstatementLR\tstatementRL\tverdict\tnote",
  ...rows.map(r => [r.v.id, r.v.renderLeft, r.v.renderRight, String(r.v.subLR), String(r.v.subRL), "-", "-",
    cell(r.lr), cell(r.rl), r.verdict, r.note].join("\t")), ""].join("\n")
writeFileSync(join(here, "record-assignability.tsv"), text)
const counts = new Map<string, number>()
for (const r of rows) counts.set(r.verdict, (counts.get(r.verdict) ?? 0) + 1)
const caught = rows.filter(r => r.lr !== null && r.rl !== null && r.v.subLR === r.lr && r.v.subRL === r.rl &&
  (r.v.mutantLR !== r.lr || r.v.mutantRL !== r.rl)).map(r => r.v.id)
console.log(`tsgo ${version}; tsgo exit ${run.exitCode}`)
console.log(`pairs ${rows.length}; ` + [...counts.entries()].sort().map(([k, n]) => `${k} ${n}`).join(", "))
console.log(`red control (written-order record arm) caught by: ${caught.join(", ") || "none"}`)
for (const r of rows) console.log(`${r.verdict}\t${r.v.id}\tLR ${cell(r.lr)} RL ${cell(r.rl)}\t${r.note}`)
if (rows.some(r => r.verdict === "defect" || r.verdict === "refused") || !caught.length) process.exit(1)
