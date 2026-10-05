// Seat A401 (2026-10-05). Does one Effect build export every API head that the generated target
// profile names? A finite check of names and kinds, not of behaviour.
//
// Run: EFFECT_DIR=<an effect package directory> PROFILE=<profile.json> bun profile-heads.mjs
// PROFILE is the JSON text of `ts/eff/profile.gen.ts` (the `heads` list, and the `cite` and
// `target` fields of its rows). The build is loaded by directory.
import { existsSync, readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR
const version = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const profile = JSON.parse(readFileSync(process.env.PROFILE, "utf8"))
const index = await import(`${dir}/dist/index.js`)

const kindOf = (head) => {
  const [module, ...rest] = head.split(".")
  let value = index[module]
  if (value === undefined) return `no module ${module}`
  for (const name of rest) {
    value = value?.[name]
    if (value === undefined) return "missing"
  }
  return typeof value === "function" ? `function/${value.length}` : typeof value
}

const heads = {}
for (const head of profile.heads) heads[head] = kindOf(head)

// The package entry points that the tree's generated TypeScript imports.
const entries = {}
for (const entry of ["unstable/sql", "unstable/persistence", "sql", "persistence", "unstable/sql/SqlClient", "sql/SqlClient",
  "unstable/persistence/KeyValueStore", "persistence/KeyValueStore", "testing/TestClock", "Queue", "TxRef"]) {
  entries[entry] = existsSync(`${dir}/dist/${entry}.js`) || existsSync(`${dir}/dist/${entry}/index.js`) ? "present" : "absent"
}
console.log(JSON.stringify({ effect: version, heads, entries }, null, 1))
