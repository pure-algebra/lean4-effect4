// Numbers seat, probe 6: the Lean TypeScript model against a JavaScript engine.
//
// Reads model-vectors.txt (written by ../Models.lean: `op a b model` per line, `a` and `b`
// already doubles) and recomputes each with the generated prelude atoms on the same doubles.
// `round n` is checked against `Number(BigInt(n))`, JavaScript's own nearest double. Prints
// the number of lines and of differences per operation, and the first differences.
//   cd harness/truth && bun -e "$(cat <this file>)"
// The vector path is absolute so the working directory can stay harness/truth.

import { readFileSync } from "node:fs"
import { add, sub, mul, div } from "./prelude-atoms.gen.ts"

// VECTORS selects the file; the red control is trunc-vectors.txt, which must show differences.
const file = process.env.VECTORS ??
  "/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-30-pass/numbers/ts/model-vectors.txt"
console.log(`file ${file.split("/").pop()}`)
const lines = readFileSync(file, "utf8").split("\n").filter((l) => l.length > 0)
const counts: Record<string, { n: number; bad: number }> = {}
const firstBad: string[] = []
for (const line of lines) {
  const [op, as, bs, ms] = line.split(" ")
  const a = Number(BigInt(as!)), b = Number(BigInt(bs!))
  if (op !== "round" && (BigInt(a) !== BigInt(as!) || BigInt(b) !== BigInt(bs!)))
    throw new Error(`not a double: ${line}`)
  const got =
    op === "round" ? Number(BigInt(as!)) :
    op === "add" ? add(a, b) :
    op === "mul" ? mul(a, b) :
    op === "sub" ? sub(a, b) :
    op === "div" ? div(a, b) : NaN
  const c = (counts[op!] ??= { n: 0, bad: 0 })
  c.n++
  if (!Number.isFinite(got) || BigInt(got) !== BigInt(ms!)) {
    c.bad++
    if (firstBad.length < 5) firstBad.push(`${line} js=${Number.isFinite(got) ? BigInt(got) : got}`)
  }
}
console.log(`vectors ${lines.length}`)
for (const [op, c] of Object.entries(counts)) console.log(`  ${op.padEnd(5)} ${c.n} lines, ${c.bad} differ`)
for (const s of firstBad) console.log(`  first difference: ${s}`)
