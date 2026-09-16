#!/usr/bin/env bun
/**
 * The type oracle over a corpus manifest: every well-typed program's answer, error and
 * requirement types, as Lean rendered them, against the types `tsc` infers for the printed
 * module, both assignment directions (`oracle.ts`). The same comparison `cli.ts` runs on the
 * hand-picked selection, on every program of a manifest written by
 * `harness/truth/Truth.lean --corpus`; `scripts/check-corpus.py` calls it.
 *
 *     bun tools/target/corpus.ts --repo . --manifest <corpus.json> --inferred <dir> --out <report.json>
 *
 * The module read is the program's *unannotated* block (`inferred/<name>.ts`, written by
 * `run-truth.ts --emit` from the manifest's `declInferred`): `typeof Program.main` is then
 * what the host's compiler infers for the printed initializer on its own. Reading the shipped
 * annotated block would hand Lean's rendered type back to the comparison (the annotation *is*
 * that type), which the audit of 2026-09-13 showed reports agreement on a widened annotation.
 *
 * A required service key is bound the way the printed program spells it: a key printed as
 * `Context.Service<shape>("k<name>_<service>")` is, on rc.112, a requirement of exactly its
 * shape type (`Context.Service<Identifier, Shape = Identifier>`), so the manifest's per-key
 * `shape` is its carrier. The selection's adapter handles take precedence for the keys they
 * name. Two keys of one shape collapse into one host type; that is a `noninjective` refusal,
 * reported by reason, never an agreement (DI-24, DI-76).
 *
 * A program the printer refused, or whose requirement row names a key with no binding, is
 * reported as `refused` with the reason; an ill-typed program is not queried.
 */
import { mkdirSync, readFileSync, writeFileSync } from "node:fs"
import { dirname, resolve } from "node:path"
import { bindRendered, key, requirements } from "./profile.ts"
import { query, type Query } from "./oracle.ts"

const args = process.argv.slice(2)
let repo = resolve(import.meta.dir, "../.."), manifestPath = "", inferred = "", output = ""
for (let i = 0; i < args.length; i++) {
  const arg = args[i], value = args[++i]
  if (!value) throw new Error(`missing value for ${arg}`)
  if (arg === "--repo") repo = resolve(value)
  else if (arg === "--manifest") manifestPath = resolve(value)
  else if (arg === "--inferred") inferred = resolve(value)
  else if (arg === "--out") output = resolve(value)
  else throw new Error(`unknown option ${arg}`)
}
if (!manifestPath || !inferred || !output) throw new Error("--manifest, --inferred and --out are required")

const manifest = JSON.parse(readFileSync(manifestPath, "utf8"))
const selection = JSON.parse(readFileSync(resolve(repo, "Test/fixtures/target/selection.json"), "utf8"))
const handles = new Map<string, string>(Object.entries(selection.handles as Record<string, string>))
const scope = key(manifest.scopeKey)
const imports = [
  'import type { Option, Result, Exit, Cause, Fiber, Scope, Context, Ref, Deferred } from "effect"',
  `import type * as Adapter from ${JSON.stringify(resolve(repo, "harness/truth/prelude.ts"))}`
]
/** The carrier of each required key: the adapter handle the selection binds it to, else the
 * shape the manifest renders for it (the host's own requirement type for the printed key). */
const bindings = (requires: Array<Record<string, unknown>>): Map<string, string> => {
  const bound = new Map<string, string>()
  for (const item of requires) {
    const k = key(item), id = `${k.name}:${k.service}`
    const adapter = handles.get(id)
    if (adapter !== undefined) bound.set(id, adapter)
    else if (typeof item.shape === "string") bound.set(id, item.shape)
  }
  return bound
}
const queries: Query[] = []
for (const entry of manifest.programs as Array<Record<string, any>>) {
  if (!entry.wellTyped || entry.decl === null) continue
  const source = resolve(inferred, `${entry.name}.ts`)
  const q: Query = {
    id: `program/${entry.name}`, source,
    imports: [...imports, `import type * as Program from ${JSON.stringify(source)}`],
    subject: "typeof Program.main", kind: "program", expected: {}, inputIssues: [],
    provenance: { metadata: "corpus manifest", program: entry.name, type: entry.type, module: "inferred (unannotated)" }
  }
  if (entry.declInferred === null) q.inputIssues!.push({ code: "no-inferred-module", message: "the manifest has no unannotated block for a well-typed program" })
  try {
    q.expected.A = bindRendered(entry.type.answer, handles)
    q.expected.E = bindRendered(entry.type.error, handles)
    q.expected.R = requirements(entry.type.requires, scope, bindings(entry.type.requires))
  } catch (error) {
    q.inputIssues!.push({ code: "program-type-metadata", message: String(error) })
  }
  queries.push(q)
}
const report = query(repo, queries, "effect@4.0.0-rc.112/corpus")
mkdirSync(dirname(output), { recursive: true })
writeFileSync(output, JSON.stringify(report, null, 2) + "\n")
const count = (status: string) => report.observations.filter(o => o.status === status).length
console.log(`corpus types: ${queries.length} queried; ${count("agree")} agree, ${count("mismatch")} mismatch, ${count("refused")} refused`)
