// Seat T: one-off exploration of oxc-parser 0.147.0's tree shape on the fixture (node types and the
// fields this census reads). Output: logs/explore_oxc.log.
import { parseSync } from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/oxc-parser/src-js/index.js"
import { readFileSync } from "node:fs"
const file = process.argv[2]!
const src = readFileSync(file, "utf8")
const r = parseSync(file, src, { lang: "ts", sourceType: "module" })
console.log("errors", r.errors.length)
const types = new Map<string, number>()
const samples = new Map<string, string>()
const walk = (n: any) => {
  if (Array.isArray(n)) { n.forEach(walk); return }
  if (!n || typeof n !== "object") return
  if (typeof n.type === "string") {
    types.set(n.type, (types.get(n.type) ?? 0) + 1)
    if (!samples.has(n.type)) samples.set(n.type, Object.keys(n).join(","))
  }
  for (const k of Object.keys(n)) if (k !== "parent") walk(n[k])
}
walk(r.program)
for (const [t, c] of [...types].sort()) console.log(t, c, "|", samples.get(t))
// offsets: compare start/end against the source for a non-ASCII-free prefix
const first = r.program.body[1]
console.log("second statement span", first.start, first.end, JSON.stringify(src.slice(first.start, first.start + 20)))
