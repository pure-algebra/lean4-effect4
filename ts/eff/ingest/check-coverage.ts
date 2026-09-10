// Read the original JSON oracles; coverage is independent of both recognizers.
import { readFileSync, readdirSync } from "node:fs"
import { join } from "node:path"
import { Eff, Stmt, ActionTerm, LayerTerm } from "../eff.gen.ts"
import { rows } from "../profile.gen.ts"
import { forms } from "../forms.gen.ts"
import { nativeOpJson } from "../json.gen.ts"
const dir = process.argv[2]
if (!dir) throw new Error("check-coverage.ts <foreign-directory>")
const seen = { eff: new Set<string>(), stmt: new Set<string>(), action: new Set<string>(), layer: new Set<string>(), row: new Set<string>() }
const array = (v: unknown): readonly unknown[] => { if (!Array.isArray(v) || typeof v[0] !== "string") throw new Error("invalid oracle constructor"); return v }
function chain(v: unknown, walk: (v: unknown) => void): void { const a = array(v); if (a[0] === "nil") return; if (a[0] !== "cons") throw new Error("invalid oracle list"); walk(a[1]); chain(a[2], walk) }
function eff(v: unknown): void {
  const a = array(v), tag = String(a[0]); seen.eff.add(tag)
  switch (tag) {
    case "perform": case "callback": seen.row.add(JSON.stringify(a[1])); break
    case "suspend": case "exit": case "uninterruptible": case "interruptible": case "scoped": eff(a[1]); break
    case "bind": case "catchCause": case "onExit": case "acquireRelease": eff(a[1]); eff(a[2]); break
    case "matchCause": eff(a[1]); eff(a[2]); eff(a[3]); break
    case "branch": eff(a[2]); eff(a[3]); break
    case "whileLoop": eff(a[4]); break
    case "gen": chain(a[1], stmt); break
    case "withFiber": action(a[1]); break
    case "provideLayer": layer(a[1]); eff(a[3]); break
    case "provideService": eff(a[3]); break
  }
}
function stmt(v: unknown): void {
  const a = array(v), tag = String(a[0]); seen.stmt.add(tag)
  if (tag === "bindYield" || tag === "yieldDiscard") eff(a[1])
  if (tag === "ifElse") { chain(a[2], stmt); chain(a[3], stmt) }
  if (tag === "whileTrue") chain(a[1], stmt)
}
function action(v: unknown): void {
  const a = array(v), tag = String(a[0]); seen.action.add(tag)
  if (["fork", "forkIn", "forkScoped"].includes(tag)) eff(a[1])
  if (tag === "raceAll") chain(a[1], eff)
}
function layer(v: unknown): void {
  const a = array(v), tag = String(a[0]); seen.layer.add(tag)
  if (tag === "effect") eff(a[2])
  if (tag === "effectDiscard") eff(a[1])
  if (["provide", "provideMerge", "merge"].includes(tag)) { layer(a[1]); layer(a[2]) }
  if (tag === "fresh" || tag === "orDie") layer(a[1])
}
const files = readdirSync(dir)
for (const file of files.filter(f => f.endsWith(".json") && !f.endsWith(".keys.json"))) eff(JSON.parse(readFileSync(join(dir, file), "utf8")))
const expected = {
  eff: Object.keys(Eff.cases),
  stmt: Object.keys(Stmt.cases),
  action: Object.keys(ActionTerm.cases).filter(n => !["interruptScoped", "awaitAllFailFast", "snapshotChildren", "awaitNewChildren", "setContext"].includes(n)),
  layer: Object.keys(LayerTerm.cases),
  row: rows.map(r => JSON.stringify(nativeOpJson(r.op)))
}
for (const family of ["eff", "stmt", "action", "layer", "row"] as const) {
  const missing = expected[family].filter(n => !seen[family].has(n))
  if (missing.length) throw new Error(`missing ${family} coverage: ${missing.join(", ")}`)
}
for (const row of forms.rows) for (const depth of [0, 1, 2, 5]) {
  if (!files.includes(`baseline-form-${row.id}-${depth}.ts`)) throw new Error(`missing form/depth ${row.id}/${depth}`)
}
console.log(`PASS oracle coverage: ${seen.eff.size} Eff, ${seen.stmt.size} statements, ${seen.action.size} actions, ${seen.layer.size} layers, ${seen.row.size} native rows; ${forms.rows.length} forms at four depths`)
