// Read the original JSON oracles; coverage is independent of both recognizers.
//
// The walker has one case for each constructor of the four sorts it reads, and the compiler
// holds it to that. A node's tag is checked against the generated schema's cases (`eff.gen.ts`),
// and each switch ends in a default that takes `never`. A constructor appended in Lean reaches
// `eff.gen.ts` by regeneration (`make gen-ts`), and this file then does not type-check
// (`bun run typecheck`) until the walker has the case. Until 2026-10-06 a constructor with no
// case was a leaf without a word: the walker read no body of `restore` or of `catchIf`, and no
// layer of `mergeAll`.
import { readFileSync, readdirSync } from "node:fs"
import { join } from "node:path"
import { Eff, Stmt, ActionTerm, LayerTerm } from "../eff.gen.ts"
import { rows } from "../profile.gen.ts"
import { forms } from "../forms.gen.ts"
import { nativeOpJson } from "../json.gen.ts"
const dir = process.argv[2]
if (!dir) throw new Error("check-coverage.ts <foreign-directory>")
const seen = { eff: new Set<string>(), stmt: new Set<string>(), action: new Set<string>(), layer: new Set<string>(), row: new Set<string>() }
/** A row's coverage key: its operation. A read-modify-write row of the profile is its face, the
 * unit literal for its binder term (Lean `Signature.face`; the state plan's T5), which is closed.
 * The constructed corpus performs each face once (`tools/Drivers/ForeignCorpus.lean`
 * `nativeProbes`), so the key is exact. */
const rowKey = (op: unknown): string => JSON.stringify(op)
const array = (v: unknown): readonly unknown[] => { if (!Array.isArray(v) || typeof v[0] !== "string") throw new Error("invalid oracle constructor"); return v }
function chain(v: unknown, walk: (v: unknown) => void): void { const a = array(v); if (a[0] === "nil") return; if (a[0] !== "cons") throw new Error("invalid oracle list"); walk(a[1]); chain(a[2], walk) }
/** A node's tag, as a constructor of its sort: a name that the generated schema's cases hold. */
const tagOf = <Tag extends string>(cases: Readonly<Record<Tag, unknown>>, sort: string, a: readonly unknown[]): Tag => {
  const tag = String(a[0])
  const known = (name: string): name is Tag => Object.hasOwn(cases, name)
  if (!known(tag)) throw new Error(`an oracle holds the ${sort} constructor ${tag}, which the generated schema does not name`)
  return tag
}
/** The default of a walker's switch. Its argument has no value when every constructor has a
 * case, so a constructor with no case is refused where this file is type-checked. */
const noCase = (tag: never, sort: string): never => { throw new Error(`the coverage walker has no case for the ${sort} constructor ${String(tag)}`) }
// A node is `[tag, field, …]` in the constructor's declaration order (`json.gen.ts`).
function eff(v: unknown): void {
  const a = array(v), tag = tagOf<Eff["_tag"]>(Eff.cases, "Eff", a); seen.eff.add(tag)
  switch (tag) {
    case "succeed": case "fail": case "failCause": case "sync": case "yieldNow": case "awaitFiber": case "service": return
    case "perform": seen.row.add(rowKey(a[1])); return
    case "suspend": case "exit": case "uninterruptible": case "interruptible": case "scoped": eff(a[1]); return
    case "bind": case "catchCause": case "onExit": case "acquireRelease": eff(a[1]); eff(a[2]); return
    case "matchCause": eff(a[1]); eff(a[2]); eff(a[3]); return
    case "catchIf": eff(a[2]); eff(a[3]); return
    case "select": eff(a[3]); eff(a[4]); return
    case "iterate": eff(a[6]); return
    case "restore": eff(a[2]); return
    case "gen": chain(a[1], stmt); return
    case "withFiber": action(a[1]); return
    case "provideLayer": layer(a[1]); eff(a[3]); return
    case "provideService": eff(a[3]); return
    case "defs": chain(a[2], eff); eff(a[3]); return
    default: return noCase(tag, "Eff")
  }
}
function stmt(v: unknown): void {
  const a = array(v), tag = tagOf<Stmt["_tag"]>(Stmt.cases, "Stmt", a); seen.stmt.add(tag)
  switch (tag) {
    case "ret": case "breakLoop": return
    case "bindYield": case "yieldDiscard": eff(a[1]); return
    case "ifElse": chain(a[2], stmt); chain(a[3], stmt); return
    case "whileTrue": chain(a[1], stmt); return
    default: return noCase(tag, "Stmt")
  }
}
function action(v: unknown): void {
  const a = array(v), tag = tagOf<ActionTerm["_tag"]>(ActionTerm.cases, "ActionTerm", a); seen.action.add(tag)
  switch (tag) {
    case "runIn": case "interrupt": case "interruptScoped": case "interruptAll": case "awaitAll": case "awaitAllFailFast":
    case "snapshotChildren": case "awaitNewChildren": case "setContext": case "getContext": case "getId": case "closeScope":
    case "getInterruptible": return
    case "fork": case "forkIn": case "forkScoped": eff(a[1]); return
    case "raceAll": chain(a[1], eff); return
    default: return noCase(tag, "ActionTerm")
  }
}
function layer(v: unknown): void {
  const a = array(v), tag = tagOf<LayerTerm["_tag"]>(LayerTerm.cases, "LayerTerm", a); seen.layer.add(tag)
  switch (tag) {
    case "succeed": case "ref": return
    case "effect": eff(a[2]); return
    case "effectDiscard": eff(a[1]); return
    case "provide": case "provideMerge": case "merge": layer(a[1]); layer(a[2]); return
    case "fresh": case "orDie": layer(a[1]); return
    case "mergeAll": chain(a[1], layer); return
    default: return noCase(tag, "LayerTerm")
  }
}
const files = readdirSync(dir)
for (const file of files.filter(f => f.endsWith(".json") && !f.endsWith(".keys.json"))) eff(JSON.parse(readFileSync(join(dir, file), "utf8")))
const expected = {
  eff: Object.keys(Eff.cases),
  stmt: Object.keys(Stmt.cases),
  action: Object.keys(ActionTerm.cases).filter(n => !["interruptScoped", "awaitAllFailFast", "snapshotChildren", "awaitNewChildren", "setContext"].includes(n)),
  layer: Object.keys(LayerTerm.cases),
  row: rows.map(r => rowKey(nativeOpJson(r.op)))
}
// The key must keep the profile's rows apart, or a missing name would hide behind another.
if (new Set(expected.row).size !== rows.length) throw new Error("the row coverage key collapses two profile rows")
for (const family of ["eff", "stmt", "action", "layer", "row"] as const) {
  const missing = expected[family].filter(n => !seen[family].has(n))
  if (missing.length) throw new Error(`missing ${family} coverage: ${missing.join(", ")}`)
}
for (const row of forms.rows) for (const depth of [0, 1, 2, 5]) {
  if (!files.includes(`baseline-form-${row.id}-${depth}.ts`)) throw new Error(`missing form/depth ${row.id}/${depth}`)
}
console.log(`PASS oracle coverage: ${seen.eff.size} Eff, ${seen.stmt.size} statements, ${seen.action.size} actions, ${seen.layer.size} layers, ${seen.row.size} native rows; ${forms.rows.length} forms at four depths`)
