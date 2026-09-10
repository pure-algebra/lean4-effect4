/** Selection contains identities/bindings only. Expected columns come from generated Lean data. */
import * as ts from "../../ts/eff/node_modules/typescript/lib/typescript.js"
import * as Schema from "../../ts/eff/node_modules/effect/dist/Schema.js"
import { Row, type Ty } from "../../ts/eff/eff.gen.ts"
import { packages } from "../../ts/eff/packages.gen.ts"
import { readFileSync } from "node:fs"
import { resolve } from "node:path"
import { createHash } from "node:crypto"
import { query, type Query, type Issue, type Report } from "./oracle.ts"

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
export function requirements(raw: unknown, scope: Key | undefined, bindings: ReadonlyMap<string, string> = new Map()): string {
  const carriers = new Map<string, string>()
  for (const item of array(raw, "full requires metadata")) {
    const k = key(item), id = keyId(k)
    const carrier = scope && keyId(scope) === id ? "Scope.Scope" : bindings.get(id)
    if (!carrier) throw new Error(`unbound service key ${id}; no fallback from service code alone`)
    const prior = carriers.get(carrier)
    if (prior && prior !== id) throw new Error(`noninjective service binding: ${prior} and ${id} both map to ${carrier}`)
    carriers.set(carrier, id)
  }
  return [...carriers.keys()].map(t => `(${t})`).join(" | ") || "never"
}

/** Public AST transform binds canonical target names; no textual substring substitutions. */
export function bindRendered(text: string, handles: ReadonlyMap<string, string>): string {
  const syntax = ts.transpileModule(`type Expected = ${text}`, { reportDiagnostics: true }).diagnostics ?? []
  if (syntax.some(d => d.category === ts.DiagnosticCategory.Error)) throw new Error("invalid rendered type syntax")
  const sf = ts.createSourceFile("type.ts", `type Expected = ${text}`, ts.ScriptTarget.Latest, true)
  const first = sf.statements[0]
  if (sf.statements.length !== 1 || !first || !ts.isTypeAliasDeclaration(first)) throw new Error("invalid rendered type expression")
  const qualified = (name: ts.EntityName): string => ts.isIdentifier(name) ? name.text : `${qualified(name.left)}.${name.right.text}`
  const entity = (text: string): ts.EntityName => {
    const parts = text.split(".")
    if (!parts.every(p => /^[A-Za-z_$][\w$]*$/.test(p))) throw new Error(`invalid qualified target binding ${text}`)
    return parts.slice(1).reduce<ts.EntityName>((left, p) => ts.factory.createQualifiedName(left, p), ts.factory.createIdentifier(parts[0]!))
  }
  const transformed = ts.transform(first.type, [context => root => {
    const visit: ts.Visitor = node => {
      if (ts.isTypeReferenceNode(node)) {
        const target = handles.get(qualified(node.typeName))
        if (target) return ts.factory.updateTypeReferenceNode(node, entity(target), node.typeArguments && ts.factory.createNodeArray(node.typeArguments.map(arg => ts.visitNode(arg, visit, ts.isTypeNode)!)))
      }
      return ts.visitEachChild(node, visit, context)
    }
    return ts.visitNode(root, visit, ts.isTypeNode)!
  }])
  const result = ts.createPrinter().printNode(ts.EmitHint.Unspecified, transformed.transformed[0]!, sf)
  transformed.dispose()
  return result
}

/** Projection of the generated Ty schema to the target's type syntax, never per-case expected types. */
export function renderTy(ty: Ty, handles: ReadonlyMap<string, string>): string {
  const r = (t: Ty) => renderTy(t, handles)
  switch (ty._tag) {
    case "never": return "never"
    case "unit": return "void"
    case "nat": case "int": return "number"
    case "string": return "string"
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

/** A method's actual receiver is derived from its selected member type, not a second claim. */
export function receiverOfSubject(subject: string): string | undefined {
  const sf = ts.createSourceFile("subject.ts", `type Subject = ${subject}`, ts.ScriptTarget.Latest, true)
  const first = sf.statements[0]
  if (first && ts.isTypeAliasDeclaration(first) && ts.isIndexedAccessTypeNode(first.type)) {
    return ts.createPrinter().printNode(ts.EmitHint.Unspecified, first.type.objectType, sf)
  }
  return undefined
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
      subject: "typeof Program.main", kind: "effect", expected: {}, inputIssues: [...inputIssues], provenance: { metadata: "harness/truth/corpus.json", program: name } }
    const entry = entries.find(p => p.name === name)
    q.provenance = { metadata: "harness/truth/corpus.json", program: name, type: entry?.type ?? null, scopeKey: scope ?? null, handles: Object.fromEntries(handles) }
    try {
      const types = object(entry?.type, `${name}.type`)
      for (const [axis, field] of [["A", "answer"], ["E", "error"]] as const) {
        q.expected[axis] = bindRendered(string(types[field], `${name}.${field}`), handles)
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
  for (const selected of selectedRows) {
    const table = string(selected.table, "table"), name = string(selected.name, "row name")
    const q: Query = { id: `row/${table}/${name}`, source: "harness/truth/prelude.ts", imports,
      subject: string(selected.subject, "row subject"), kind: "function", expected: {}, inputIssues: [...inputIssues, ...rowInventoryIssues],
      provenance: { metadata: table === "Host" ? "harness/truth/corpus.json#hostRows" : "ts/eff/packages.gen.ts", table, row: name } }
    const receiver = receiverOfSubject(q.subject)
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
  }
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
  for (const file of ["Test/fixtures/target/selection.json", "harness/truth/corpus.json", "ts/eff/packages.gen.ts", "ts/eff/eff.gen.ts", "tools/target/oracle.ts", "tools/target/profile.ts", "tools/target/input.ts", "tools/target/cli.ts", "scripts/check-target.py"]) {
    try { report.sourceHashes[file] = createHash("sha256").update(readFileSync(resolve(repo, file))).digest("hex") }
    catch { report.sourceHashes[file] = "missing" }
  }
  return report
}
