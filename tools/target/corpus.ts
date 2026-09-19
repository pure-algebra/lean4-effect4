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
 * A required service key is bound by the shape the manifest renders beside it, by the one rule
 * both type lanes share (`requirements` in `profile.ts`, DI-93). Two keys of one shape collapse
 * into one host type; that is a `noninjective` refusal, reported by reason, never an agreement
 * (DI-24, DI-76).
 *
 * A program the printer refused, or whose requirement row names a key with no binding, is
 * reported as `refused` with the reason; an ill-typed program is not queried.
 */
import { mkdirSync, readFileSync, writeFileSync } from "node:fs"
import { dirname, resolve } from "node:path"
import { key, requirements } from "./profile.ts"
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
const queries: Query[] = []
for (const entry of manifest.programs as Array<Record<string, any>>) {
  if (!entry.wellTyped || entry.decl === null) continue
  const source = resolve(inferred, `${entry.name}.ts`)
  const q: Query = {
    id: `program/${entry.name}`, source,
    imports: [...imports, `import type * as Program from ${JSON.stringify(source)}`],
    subject: "typeof Program.main", kind: "program", expected: {}, bindings: Object.fromEntries(handles), inputIssues: [],
    provenance: { metadata: "corpus manifest", program: entry.name, type: entry.type, module: "inferred (unannotated)" }
  }
  if (entry.declInferred === null) q.inputIssues!.push({ code: "no-inferred-module", message: "the manifest has no unannotated block for a well-typed program" })
  try {
    q.expected.A = entry.type.answer
    q.expected.E = entry.type.error
    q.expected.R = requirements(entry.type.requires, scope)
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
