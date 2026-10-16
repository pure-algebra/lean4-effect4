/** The named-types probe: the compiler half and the Schema half.
 *
 * Run in `ts/eff`: `bun probe/named-types/run.ts`. The compiler half runs the pinned tsgo once
 * over `cases/` and compares each file's error codes, as a multiset, with the codes its first
 * line expects (`// expect: none` or `// expect: TS2456 TS2456`). The Schema half runs
 * `documents.run.ts` on rc.112. Each is a finite observation of the pinned host, not a proof. */
import { readdirSync, readFileSync } from "node:fs"
import { join } from "node:path"

const here = import.meta.dir
const tsgo = join(here, "../../node_modules/.bin/tsgo")
const compiled = Bun.spawnSync([tsgo, "--noEmit", "-p", join(here, "tsconfig.json"), "--pretty", "false"], { cwd: here })
const output = compiled.stdout.toString() + compiled.stderr.toString()
const found = new Map<string, string[]>()
const outside: string[] = []
for (const line of output.split("\n")) {
  const hit = /^(?:.*\/)?(cases\/[^(]+)\(\d+,\d+\): error (TS\d+):/.exec(line)
  if (hit) found.set(hit[1]!, [...(found.get(hit[1]!) ?? []), hit[2]!])
  else if (/: error TS\d+:/.test(line)) outside.push(line)
}
const sorted = (codes: readonly string[]) => [...codes].sort().join(" ")
let mismatches = 0, files = 0, codes = 0
for (const name of readdirSync(join(here, "cases")).filter(n => n.endsWith(".ts")).sort()) {
  const file = `cases/${name}`
  const head = readFileSync(join(here, file), "utf8").split("\n")[0]!
  const expected = /^\/\/ expect: (.*)$/.exec(head)?.[1]
  if (expected === undefined) throw new Error(`${file}: no expect line`)
  const want = expected === "none" ? [] : expected.split(" ")
  const got = found.get(file) ?? []
  files++; codes += got.length
  const ok = sorted(want) === sorted(got)
  if (!ok) mismatches++
  console.log(`${ok ? "ok  " : "FAIL"} ${file}: expected [${sorted(want)}], tsgo [${sorted(got)}]`)
}
for (const line of outside) { mismatches++; console.log(`FAIL a diagnostic outside the cases: ${line}`) }
if (mismatches > 0) { console.log(output); throw new Error(`${mismatches} case(s) disagree with tsgo`) }
console.log(`PASS named-types compiler: ${files} case files, ${codes} expected diagnostics, tsgo ${
  Bun.spawnSync([tsgo, "--version"]).stdout.toString().trim()}`)

const documents = Bun.spawnSync(["bun", join(here, "documents.run.ts")], { cwd: here })
const last = documents.stdout.toString().trim().split("\n").at(-1)
if (documents.exitCode !== 0) { console.log(documents.stdout.toString(), documents.stderr.toString()); throw new Error("documents probe failed") }
console.log(last)
