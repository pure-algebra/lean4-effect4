/** Selection contains identities/bindings only. Expected columns come from generated Lean data. */
import * as Schema from "../../ts/eff/node_modules/effect/dist/Schema.js"
import { Row, type Ty } from "../../ts/eff/eff.gen.ts"
import { packages } from "../../ts/eff/packages.gen.ts"
import { readFileSync } from "node:fs"
import { resolve } from "node:path"
import { createHash } from "node:crypto"
import { query, subjectReceivers, type Query, type Issue, type Report } from "./oracle.ts"

type Obj = Record<string, unknown>
function object(x: unknown, label: string): Obj {
  if (!x || typeof x !== "object" || Array.isArray(x)) throw new Error(`${label}: expected object`)
  return x as Obj
}
function array(x: unknown, label: string): unknown[] {
  if (!Array.isArray(x)) throw new Error(`${label}: expected array`)
  return x
}
function string(x: unknown, label: string): string {
  if (typeof x !== "string" || !x.trim()) throw new Error(`${label}: expected nonempty string`)
  return x
}
const json = (path: string): unknown => JSON.parse(readFileSync(path, "utf8"))
export interface Key { name: number; service: number }
export function key(x: unknown): Key {
  const o = object(x, "service key")
  for (const field of ["name", "service"]) {
    if (typeof o[field] !== "number" || !Number.isSafeInteger(o[field]) || o[field] < 0) throw new Error(`invalid service key ${field}: expected safe natural number`)
  }
  return { name: o.name as number, service: o.service as number }
}
const keyId = (k: Key) => `${k.name}:${k.service}`
/** The requirement row as the host's type, the one binding rule of both type lanes (DI-93).
 * The scope key is `Scope.Scope`. Any other key is bound the way the printed program spells it:
 * a key printed as `Context.Service<shape>("k<name>_<service>")` is, on rc.112, a requirement of
 * exactly its shape type (`Context.Service<Identifier, Shape = Identifier>`), so the carrier is
 * the `shape` the manifest renders beside the key (`harness/truth/Truth.lean`, `requireJson`),
 * with handle names bound as on the answer and error axes. A key with no shape is unbound: an
 * input issue, never a fallback from the service code. Two keys of one carrier collapse into one
 * host type: a `noninjective` refusal, never an agreement (DI-24, DI-76). */
export function requirements(raw: unknown, scope: Key | undefined): string {
  const carriers = new Map<string, string>()
  for (const item of array(raw, "full requires metadata")) {
    const k = key(item), id = keyId(k), shape = object(item, "service key").shape
    const carrier = scope && keyId(scope) === id ? "Scope.Scope"
      : typeof shape === "string" && shape.trim() ? shape : undefined
    if (!carrier) throw new Error(`unbound service key ${id}; no fallback from service code alone`)
    const prior = carriers.get(carrier)
    if (prior && prior !== id) throw new Error(`noninjective service binding: ${prior} and ${id} both map to ${carrier}`)
    carriers.set(carrier, id)
  }
  return [...carriers.keys()].map(t => `(${t})`).join(" | ") || "never"
}

/** Projection of the generated Ty schema to the target's type syntax, never per-case expected types. */
export function renderTy(ty: Ty, handles: ReadonlyMap<string, string>): string {
  const r = (t: Ty) => renderTy(t, handles)
  switch (ty._tag) {
    case "never": return "never"
    case "unit": return "void"
    case "nat": case "int": return "number"
    case "string": return "string"
    case "lit": return JSON.stringify(ty.value)
    case "bool": return "boolean"
    case "handle": {
      const bound = handles.get(ty.target)
      if (!bound) throw new Error(`unbound handle target ${ty.target}`)
      return bound
    }
    case "option": return `Option.Option<${r(ty.inner)}>`
    case "list": return `ReadonlyArray<${r(ty.inner)}>`
    case "prod": return `readonly [${r(ty.left)}, ${r(ty.right)}]`
    case "except": return `Result.Result<${r(ty.value)}, ${r(ty.error)}>`
    case "exitOf": return `Exit.Exit<${r(ty.value)}, ${r(ty.error)}>`
    case "causeOf": return `Cause.Cause<${r(ty.error)}>`
    case "fiberOf": return `Fiber.Fiber<${r(ty.value)}, ${r(ty.error)}>`
    case "union": return `(${r(ty.left)}) | (${r(ty.right)})`
  }
}
export function rowArguments(row: Row, handles: ReadonlyMap<string, string>): { request: string; receiver?: string } {
  if (row.trailing.length || row.typeArgs.length) throw new Error("unsupported trailing arguments or explicit type arguments")
  const r = (t: Ty) => renderTy(t, handles)
  const spread = (t: Ty) => t._tag === "unit" ? "[]" : t._tag === "prod" ? `[${r(t.left)}, ${r(t.right)}]` : `[${r(t)}]`
  switch (row.shape) {
    case "call": return { request: row.request._tag === "unit" ? "[]" : `[${r(row.request)}]` }
    case "tupleCall":
      if (row.request._tag !== "prod") throw new Error("tupleCall request must be a binary product")
      return { request: spread(row.request) }
    case "method": {
      if (row.request._tag !== "prod") throw new Error("method request must contain receiver and arguments")
      return { request: spread(row.request.right), receiver: r(row.request.left) }
    }
    case "value": throw new Error("value row is not a callable adapter row")
  }
}

/** A method's actual receiver is derived from its selected member type, not a second claim: the
 * compiler parses the subject and answers the object type of `X["m"]`. One parse per batch. */
export function receiverOfSubject(repo: string, subject: string): string | undefined {
  return subjectReceivers(repo, [subject])[0]
}

export function queriesFromInputs(repo: string, selectionInput: unknown, corpusInput: unknown, packageInput: readonly { name: string; rows: readonly unknown[] }[] = packages): Query[] {
  const selection = object(selectionInput, "selection")
  const programs = array(selection.programs, "selected programs").map(p => string(p, "program ID"))
  const selectedRows = array(selection.rows, "selected rows").map(r => object(r, "row selection"))
  const handles = new Map(Object.entries(object(selection.handles, "handle bindings")).map(([k, v]) => [k, string(v, k)]))
  const corpus = object(corpusInput, "truth corpus")
  const entries = array(corpus.programs, "truth programs").map(p => object(p, "truth program"))
  const actualNames = entries.map(e => string(e.name, "truth program name"))
  const inputIssues: Issue[] = []
  const missing = programs.filter(p => !actualNames.includes(p)), extra = actualNames.filter(p => !programs.includes(p))
  if (missing.length || extra.length || new Set(actualNames).size !== actualNames.length) inputIssues.push({ code: "program-inventory", message: `missing=${missing.join(",")} extra=${extra.join(",")} duplicate=${new Set(actualNames).size !== actualNames.length}` })
  let scope: Key | undefined
  try { scope = key(corpus.scopeKey) } catch (e) { inputIssues.push({ code: "scope-key-metadata", message: String(e) }) }
  const imports = [
    'import type { Option, Result, Exit, Cause, Fiber, Scope, Context, Ref, Deferred } from "effect"',
    `import type * as Adapter from ${JSON.stringify(resolve(repo, "harness/truth/prelude.ts"))}`,
  ]
  const queries: Query[] = programs.map(name => {
    if (!/^[A-Za-z_$][\w$]*$/.test(name)) throw new Error(`invalid program ID ${name}`)
    const source = `harness/truth/generated/${name}.ts`
    const q: Query = { id: `program/${name}`, source, imports: [...imports, `import type * as Program from ${JSON.stringify(resolve(repo, source))}`],
      subject: "typeof Program.main", kind: "program", expected: {}, bindings: Object.fromEntries(handles), inputIssues: [...inputIssues], provenance: { metadata: "harness/truth/corpus.json", program: name } }
    const entry = entries.find(p => p.name === name)
    q.provenance = { metadata: "harness/truth/corpus.json", program: name, type: entry?.type ?? null, scopeKey: scope ?? null, handles: Object.fromEntries(handles) }
    try {
      const types = object(entry?.type, `${name}.type`)
      for (const [axis, field] of [["A", "answer"], ["E", "error"]] as const) {
        q.expected[axis] = string(types[field], `${name}.${field}`)
      }
      q.expected.R = requirements(types.requires, scope)
    } catch (e) { q.inputIssues!.push({ code: "program-type-metadata", message: String(e) }) }
    return q
  })
  const tables = new Map<string, readonly unknown[]>(packageInput.map(p => [p.name, p.rows]))
  tables.set("Host", Array.isArray(corpus.hostRows) ? corpus.hostRows : [])
  const actualRows = [...tables].flatMap(([table, rows]) => rows.map(r => `${table}/${string(object(r, "row").name, "row name")}`))
  const selectedIds = selectedRows.map(r => `${string(r.table, "table")}/${string(r.name, "name")}`)
  const unselected = actualRows.filter(id => !selectedIds.includes(id))
  const rowInventoryIssues: Issue[] = unselected.length || new Set(actualRows).size !== actualRows.length ? [{ code: "row-inventory", message: `unselected=${unselected.join(",")}; duplicate=${new Set(actualRows).size !== actualRows.length}` }] : []
  const rowReceivers = subjectReceivers(repo, selectedRows.map(r => string(r.subject, "row subject")))
  selectedRows.forEach((selected, index) => {
    const table = string(selected.table, "table"), name = string(selected.name, "row name")
    const q: Query = { id: `row/${table}/${name}`, source: "harness/truth/prelude.ts", imports,
      subject: string(selected.subject, "row subject"), kind: "function", expected: {}, bindings: Object.fromEntries(handles), inputIssues: [...inputIssues, ...rowInventoryIssues],
      provenance: { metadata: table === "Host" ? "harness/truth/corpus.json#hostRows" : "ts/eff/packages.gen.ts", table, row: name } }
    const receiver = rowReceivers[index]
    if (receiver !== undefined) q.receiver = receiver
    try {
      const raw = tables.get(table)?.find(r => object(r, "row").name === name)
      if (!raw) throw new Error(`missing selected row ${table}/${name}`)
      const row = Schema.decodeUnknownSync(Row)(raw)
      q.provenance = { metadata: table === "Host" ? "harness/truth/corpus.json#hostRows" : "ts/eff/packages.gen.ts", table, row: name, descriptor: row, scopeKey: scope ?? null, handles: Object.fromEntries(handles) }
      const args = rowArguments(row, handles)
      q.expected = { A: renderTy(row.answer, handles), E: renderTy(row.error, handles),
        R: requirements(row.requires.map(k => ({ name: k.name.value, service: k.service.value })), scope), ...args }
      if (args.receiver !== undefined && q.receiver === undefined) throw new Error("missing actual receiver binding")
      if (args.receiver === undefined && q.receiver !== undefined) throw new Error("unexpected receiver binding for non-method row")
    } catch (e) { q.inputIssues!.push({ code: "row-type-metadata", message: String(e) }) }
    queries.push(q)
  })
  return queries
}

export function repositoryQueries(repo: string): Query[] {
  if (resolve(repo) !== resolve(import.meta.dir, "../..")) throw new Error("repo must match the tool checkout and its pinned generated schemas")
  const selection = json(resolve(repo, "Test/fixtures/target/selection.json"))
  let corpus: unknown
  try { corpus = json(resolve(repo, "harness/truth/corpus.json")) }
  catch (error) {
    const queries = queriesFromInputs(repo, selection, { programs: [] })
    for (const q of queries) q.inputIssues!.push({ code: "missing-corpus-input", message: String(error).replaceAll(repo, "<repo>") })
    return queries
  }
  return queriesFromInputs(repo, selection, corpus)
}

export function repositoryReport(repo: string): Report {
  const report = query(repo, repositoryQueries(repo))
  for (const file of ["Test/fixtures/target/selection.json", "harness/truth/corpus.json", "ts/eff/packages.gen.ts", "ts/eff/eff.gen.ts", "tools/target/oracle.ts", "tools/target/checker.ts", "tools/target/profile.ts", "tools/target/input.ts", "tools/target/cli.ts"]) {
    try { report.sourceHashes[file] = createHash("sha256").update(readFileSync(resolve(repo, file))).digest("hex") }
    catch { report.sourceHashes[file] = "missing" }
  }
  return report
}
