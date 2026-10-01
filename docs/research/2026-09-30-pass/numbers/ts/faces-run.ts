// Numbers seat, probe 3: the TypeScript face.
//
// Run from harness/truth so `effect` (rc.112) and the generated atoms resolve there, and so
// nothing is written anywhere:
//   cd harness/truth && bun -e "$(cat <this file>)"
//
// `program` below is the printer's output for Faces.lean's `program`, pasted verbatim from
// faces.log line 1. The atoms are the generated prelude (harness/truth/prelude-atoms.gen.ts),
// the same functions every printed program imports. The run is rc.112's own
// `Effect.runSyncExit`.
//
// A double prints in two ways below: `js` is JavaScript's own spelling (shortest digits that
// read back to the same double), `exact` is the integer the double holds (BigInt of it).

import { Effect, Exit } from "effect"
import { add, sub, mul, div, mod, lt, pair } from "./prelude-atoms.gen.ts"

const program = Effect.flatMap(Effect.succeed(add(4503599627370496, 4503599627370497)), (a0) => Effect.flatMap(Effect.succeed(sub(a0, 9007199254740991)), (a1) => Effect.flatMap(Effect.succeed(mul(4503599627370496, 512)), (a2) => Effect.flatMap(Effect.succeed(add(a2, add(a2, 5))), (a3) => Effect.flatMap(Effect.succeed(mul(a0, 512)), (a4) => Effect.succeed(pair(a1, pair(lt(a3, 1), pair(div(a3, 2), pair(sub(sub(a3, a2), a2), mod(a4, 1000)))))))))))

const exact = (v: unknown): unknown =>
  typeof v === "number" ? (Number.isInteger(v) ? `${BigInt(v)}` : `${v}`) :
  Array.isArray(v) ? v.map(exact) : v

const exit = Effect.runSyncExit(program)
if (Exit.isSuccess(exit)) {
  console.log("rc.112 exit: success")
  console.log("  js   ", JSON.stringify(exit.value))
  console.log("  exact", JSON.stringify(exact(exit.value)))
} else {
  console.log("rc.112 exit: failure", String(exit.cause))
}

// The intermediates, one operation at a time, as the atoms compute them.
const a0 = add(4503599627370496, 4503599627370497)
const a2 = mul(4503599627370496, 512)
const a3 = add(a2, add(a2, 5))
const a4 = mul(a0, 512)
console.log("a0", `${BigInt(a0)}`, "a2", `${BigInt(a2)}`, "a3", `${BigInt(a3)}`, "a4", `${BigInt(a4)}`)
console.log("safe?", [a0, a2, a3, a4].map((x) => Number.isSafeInteger(x)))

// Two channels for one natural, 2^53 + 3 = 9007199254740995. As program text the literal is
// read round-to-nearest, ties-to-even; as a JSON number the store writes the truncated
// datum (Arch.binary64OfNat), whose exact decimal is 9007199254740994.
console.log("literal 9007199254740995 reads as", `${BigInt(9007199254740995)}`)
console.log("JSON.parse(\"9007199254740995\") is", `${BigInt(JSON.parse("9007199254740995"))}`)
console.log("JSON.parse(\"9007199254740994\") is", `${BigInt(JSON.parse("9007199254740994"))}`)

// DI-56's measured case, again: a safe input, a comparison that steers a branch.
const M = Number.MAX_SAFE_INTEGER
console.log("eq(add(M,2), succ(M)) =", add(M, 2) === M + 1, " lt(succ M, succ(succ M)) =", (M + 1) < (M + 2))

// Division and remainder on safe inputs: a finite differential against exact BigInt
// arithmetic. Deterministic generator (a 64-bit LCG, BigInt), fixed seed.
let state = 0x2026_0930n
const next = (): bigint => {
  state = (state * 6364136223846793005n + 1442695040888963407n) & ((1n << 64n) - 1n)
  return state >> 11n // 53 bits
}
const cap = (1n << 53n) - 1n
let cases = 0, divBad = 0, modBad = 0
const probe = (A: bigint, B: bigint) => {
  if (B === 0n) return
  const a = Number(A), b = Number(B)
  cases++
  if (BigInt(div(a, b)) !== A / B) divBad++
  if (BigInt(mod(a, b)) !== A % B) modBad++
}
for (let i = 0; i < 1_000_000; i++) {
  const A = next() % (cap + 1n)
  const width = next() % 54n
  const B = (next() % (1n << width)) + 1n
  probe(A, B)
}
// Edges: the largest safe dividend against every small divisor and the divisors near it.
for (let b = 1n; b <= 4096n; b++) probe(cap, b)
for (let d = 0n; d < 4096n; d++) { probe(cap, cap - d); probe(cap - d, 3n); probe(cap - d, 4n) }
console.log(`div/mod on safe inputs: ${cases} cases, div differs ${divBad}, mod differs ${modBad}`)

// The same differential past the profile: dividends above 2^53 (as doubles, the value the
// program actually holds) against exact division of that double's value.
let over = 0, overBad = 0
for (let i = 0; i < 100_000; i++) {
  const A = (1n << 53n) + (next() % (1n << 53n))
  const a = Number(A) // rounded here
  const B = (next() % 1000n) + 1n
  over++
  if (BigInt(div(a, Number(B))) !== BigInt(a) / B) overBad++
}
console.log(`div above 2^53 (on the held double): ${over} cases, differs ${overBad}`)
