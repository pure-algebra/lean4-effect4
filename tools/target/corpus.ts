#!/usr/bin/env bun
/**
 * The type oracle over a corpus manifest: every well-typed program's answer, error and
 * requirement types, as Lean rendered them, against the types `tsc` infers for the printed
 * module, both assignment directions (`oracle.ts`). The same comparison `cli.ts` runs on the
 * hand-picked selection, on every program of a manifest written by
 * `harness/truth/Truth.lean --corpus`; `scripts/check-corpus.py` calls it.
 *
 *     bun tools/target/corpus.ts --repo . --manifest <corpus.json> --generated <dir> --out <report.json>
 *
 * A program the printer refused, or whose requirement row names a service key the selection
 * does not bind, is reported as `refused`; an ill-typed program is not queried.
 */
import { mkdirSync, readFileSync, writeFileSync } from "node:fs"
import { dirname, resolve } from "node:path"
import { bindRendered, key, requirements } from "./profile.ts"
import { query, type Query } from "./oracle.ts"

const args = process.argv.slice(2)
let repo = resolve(import.meta.dir, "../.."), manifestPath = "", generated = "", output = ""
for (let i = 0; i < args.length; i++) {
  const arg = args[i], value = args[++i]
  if (!value) throw new Error(`missing value for ${arg}`)
  if (arg === "--repo") repo = resolve(value)
  else if (arg === "--manifest") manifestPath = resolve(value)
  else if (arg === "--generated") generated = resolve(value)
  else if (arg === "--out") output = resolve(value)
  else throw new Error(`unknown option ${arg}`)
}
if (!manifestPath || !generated || !output) throw new Error("--manifest, --generated and --out are required")

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
  const source = resolve(generated, `${entry.name}.ts`)
  const q: Query = {
    id: `program/${entry.name}`, source,
    imports: [...imports, `import type * as Program from ${JSON.stringify(source)}`],
    subject: "typeof Program.main", kind: "effect", expected: {}, inputIssues: [],
    provenance: { metadata: "corpus manifest", program: entry.name, type: entry.type }
  }
  try {
    q.expected.A = bindRendered(entry.type.answer, handles)
    q.expected.E = bindRendered(entry.type.error, handles)
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
