/** Compare the two faces' lines, case by case, against an expected classification, with
 * reciprocal decoding, and fail on any unexpected result.
 *
 *     bun docs/research/2026-10-19-schema-as-the-carrier/probe/compare.ts [LEAN BUN]
 *
 * Classes, one a case in `expected.tsv`: `equal` (the same text), `renamed` (the same text once
 * every fiber id is renamed by one injective map), `differ` (both executed, different text),
 * `refusedBoth` (both faces refuse: the type on both, or the value on one and the program's own
 * arithmetic on the other), `refusedLean` (Lean refuses the value while Effect encodes) and
 * `refusedEffect` (the reverse).
 * Reciprocal decoding: every Lean line of class `equal` or `renamed` decodes under the case's
 * Effect codec and encodes again to the same text. The process exits 1 on the first
 * unexpected class or failed reciprocal decode, so a deliberately altered line fails it. */
import { readFileSync } from "node:fs"
import { Schema } from "effect"
import { cases } from "./out/cases.gen.ts"

const here = import.meta.dir
const [leanPath = `${here}/out/lean.txt`, bunPath = `${here}/out/bun.txt`] = process.argv.slice(2)
const lines = (path: string): Map<string, string> =>
  new Map(readFileSync(path, "utf8").split("\n").filter(l => l.length > 0).map(l => {
    const i = l.indexOf(" ")
    return [l.slice(0, i), l.slice(i + 1)] as const
  }))
const expected = new Map(readFileSync(`${here}/expected.tsv`, "utf8").split("\n").filter(l => l.length > 0 && !l.startsWith("#")).map(l => {
  const [name, cls] = l.split("\t")
  return [name!, cls!] as const
}))
const lean = lines(leanPath), bun = lines(bunPath)

type Json = null | boolean | number | string | ReadonlyArray<Json> | { readonly [key: string]: Json }
const canon = (v: Json): string =>
  Array.isArray(v) ? `[${v.map(canon).join(",")}]`
  : v !== null && typeof v === "object" ? `{${Object.keys(v).sort().map(k => `${JSON.stringify(k)}:${canon((v as { readonly [key: string]: Json })[k] ?? null)}`).join(",")}}`
  : JSON.stringify(v)

/** One injective renaming of fiber ids across all lines: Lean id → Effect id. */
const renaming = new Map<string, string>()
const renamed = (l: string, b: string): boolean => {
  const re = /"fiberId":(\d+)/g
  const li = [...l.matchAll(re)].map(m => m[1]!), bi = [...b.matchAll(re)].map(m => m[1]!)
  if (li.length !== bi.length || l.replace(re, '"fiberId":#') !== b.replace(re, '"fiberId":#')) return false
  for (let i = 0; i < li.length; i++) {
    const have = renaming.get(li[i]!)
    if (have !== undefined && have !== bi[i]) return false
    if ([...renaming.values()].includes(bi[i]!) && have === undefined) return false
    renaming.set(li[i]!, bi[i]!)
  }
  return true
}

let failures = 0
const fail = (name: string, why: string) => { failures++; console.log(`FAIL ${name}: ${why}`) }
for (const [name, cls] of expected) {
  const l = lean.get(name), b = bun.get(name)
  if (l === undefined || b === undefined) { fail(name, "missing on one face"); continue }
  const leanRefused = l === "refused", effectRefused = b === "refused" || b.startsWith("REFUSED")
  const observed =
    leanRefused && effectRefused ? "refusedBoth"
    : leanRefused ? "refusedLean"
    : effectRefused ? "refusedEffect"
    : l === b ? "equal"
    : renamed(l, b) ? "renamed" : "differ"
  if (observed !== cls) { fail(name, `expected ${cls}, observed ${observed}`); continue }
  if (observed === "equal" || observed === "renamed") {
    const entry = cases[name]
    if (entry === undefined) { fail(name, "no codec"); continue }
    try {
      const codec = entry.codec as Schema.Codec<unknown, unknown>
      const again = canon(Schema.encodeSync(codec)(Schema.decodeUnknownSync(codec)(JSON.parse(b))) as Json)
      if (again !== b) fail(name, `reciprocal decode differs: ${again}`)
    } catch (error) { fail(name, `reciprocal decode refused: ${String(error).split("\n")[0]!.slice(0, 120)}`) }
  }
  console.log(`ok ${name} ${cls}`)
}
const counts = new Map<string, number>()
for (const cls of expected.values()) counts.set(cls, (counts.get(cls) ?? 0) + 1)
console.log(`classes: ${[...counts].map(([c, n]) => `${c} ${n}`).join(", ")}; renaming: ${[...renaming].map(([a, b]) => `${a}→${b}`).join(", ") || "none"}; failures ${failures}`)
process.exit(failures === 0 ? 0 : 1)
