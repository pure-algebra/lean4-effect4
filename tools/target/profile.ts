/** Selection contains identities/bindings only. Expected columns come from generated Lean data. */
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

/** A row's target signature as Lean rendered it (`generated/row-types.tsv`, written by
 * `tools/Tools/RowTypes.lean` with `Ty.renderRaw` and the row's own `RowShape`). There is no
 * second printer here: handle spellings stay as the row declares them and the query's
 * declarations bind them. `typeArgs` is the explicit instantiation a generic subject is queried
 * at (`<"p0">` for a `poly` atom, whose request and answer Lean rendered at the same probes),
 * empty for every other row. */
export interface RowSignature { shape: string; receiver: string; request: string; answer: string; error: string; typeArgs: string }
export function rowSignatures(repo: string): Map<string, RowSignature> {
  const table = new Map<string, RowSignature>()
  const text = readFileSync(resolve(repo, "generated/row-types.tsv"), "utf8")
  for (const line of text.split("\n")) {
    if (!line || line.startsWith("#")) continue
    const [name, row, shape, receiver, request, answer, error, typeArgs] = line.split("\t")
    if (typeArgs === undefined) throw new Error(`generated/row-types.tsv: malformed line ${JSON.stringify(line)}`)
    table.set(`${name}/${row}`, { shape: shape!, receiver: receiver!, request: request!, answer: answer!, error: error!, typeArgs })
  }
  if (!table.size) throw new Error("generated/row-types.tsv: no rows")
  return table
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
  const signatures = rowSignatures(repo)
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
      const descriptor = object(raw, "row")
      const signature = signatures.get(`${table}/${name}`)
      if (!signature) throw new Error(`generated/row-types.tsv has no signature for ${table}/${name}`)
      if (!signature.request) throw new Error(`${table}/${name} is not a callable adapter row (shape ${signature.shape}, or trailing/explicit type arguments)`)
      q.provenance = { metadata: table === "Host" ? "harness/truth/corpus.json#hostRows" : "ts/eff/packages.gen.ts", table, row: name, descriptor, rendered: signature, scopeKey: scope ?? null, handles: Object.fromEntries(handles) }
      q.expected = { A: signature.answer, E: signature.error,
        R: requirements(array(descriptor.requires, `${name}.requires`).map(k => { const o = object(k, "service key"); return { name: object(o.name, "key name").value, service: object(o.service, "key service").value } }), scope),
        request: signature.request, ...(signature.receiver ? { receiver: signature.receiver } : {}) }
      if (signature.receiver && q.receiver === undefined) throw new Error("missing actual receiver binding")
      if (!signature.receiver && q.receiver !== undefined) throw new Error("unexpected receiver binding for non-method row")
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
