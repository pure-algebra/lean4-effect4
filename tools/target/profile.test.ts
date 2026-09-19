import { expect, test } from "bun:test"
import { resolve } from "node:path"
import { readFileSync } from "node:fs"
import { key, queriesFromInputs, requirements, rowSignatures, receiverOfSubject } from "./profile.ts"
import { bindingSource } from "./oracle.ts"

const repo = resolve(import.meta.dir, "../..")
const bindings = new Map([["Host.Resource", "Adapter.HostResource"]])

test("the row signatures are Lean's, one line per selectable row, and cover the selection", () => {
  const signatures = rowSignatures(repo)
  const selection = JSON.parse(readFileSync(resolve(repo, "Test/fixtures/target/selection.json"), "utf8"))
  for (const row of selection.rows as Array<{ table: string; name: string }>) {
    expect(signatures.has(`${row.table}/${row.name}`)).toBe(true)
  }
  // the projection of a request by the row's own shape, as Lean printed it: one tuple level
  expect(signatures.get("SqliteBun/sqliteOpen")).toEqual({ shape: "call", receiver: "", request: "[string]", answer: "SqlClient.SqlClient", error: "never", typeArgs: "" })
  expect(signatures.get("KeyValueStoreMemory/kvMake")?.request).toBe("[]")
  expect(signatures.get("KeyValueStoreMemory/kvGet")).toEqual({ shape: "method", receiver: "KeyValueStore.KeyValueStore", request: "[string]", answer: "Option.Option<string>", error: "readonly [string, string]", typeArgs: "" })
  expect(signatures.get("SqliteBun/sqlUnsafe")?.request).toBe("[string, ReadonlyArray<string>]")
  // a handle keeps the spelling the row declares; the query's declarations bind it
  expect(signatures.get("Host/close")?.request).toBe("[Host.Resource]")
  // a template atom is queried at an explicit instantiation, and Lean rendered its columns there
  expect(signatures.get("Atom/getOrElse")).toEqual({ shape: "poly", receiver: "", request: '[Option.Option<"p0">, "p0"]', answer: '"p0"', error: "", typeArgs: '<"p0">' })
  expect(signatures.get("Atom/pair")?.typeArgs).toBe('<"p0", "p1">')
  expect(signatures.get("Atom/succ")?.typeArgs).toBe("")
})

test("the receiver of a selected member is the object type the compiler parsed", () => {
  expect(receiverOfSubject(repo, 'Adapter.SqlHandle["unsafe"]')).toBe("Adapter.SqlHandle")
  expect(receiverOfSubject(repo, 'Adapter.KvHandle["get"]')).toBe("Adapter.KvHandle")
  expect(receiverOfSubject(repo, "typeof Adapter.Host.acquire")).toBeUndefined()
}, 60_000)

test("full requirement keys have explicit, bounded and injective target bindings", () => {
  const scope = { name: 7, service: 2 }
  expect(requirements([], scope)).toBe("never")
  expect(requirements([scope], scope)).toBe("(Scope.Scope)")
  expect(() => requirements([{ name: 8, service: 2 }], scope)).toThrow("unbound")
  expect(() => requirements(undefined, scope)).toThrow("full requires")
  expect(() => key({ name: Number.MAX_SAFE_INTEGER + 1, service: 2 })).toThrow("safe natural")
  expect(() => key({ name: -1, service: 2 })).toThrow("safe natural")
  expect(() => requirements([{ name: 1, service: 3, shape: "C.Service" }, { name: 2, service: 3, shape: "C.Service" }], scope)).toThrow("noninjective")
})

test("a required key is bound by the shape its manifest entry carries, in both lanes (DI-93)", () => {
  const scope = { name: 0, service: 0 }
  // by its shape, as the printed `Context.Service<shape>("k<name>_<service>")` requires it
  expect(requirements([{ name: 8, service: 4, shape: "number" }], scope)).toBe("(number)")
  // a handle-shaped key is carried verbatim and bound by the query's declarations
  expect(requirements([{ name: 12, service: 8, shape: "SqlClient.SqlClient" }], scope)).toBe("(SqlClient.SqlClient)")
  // no shape, no binding: `null` is what the manifest writes for a key the signature does not type
  expect(() => requirements([{ name: 8, service: 4, shape: null }], scope)).toThrow("unbound")
  // red control for the defect: a key with no shape binds nothing, whatever the handle table says
  expect(() => requirements([{ name: 8, service: 4 }], scope)).toThrow("unbound")
  // the hand-selection lane binds a program's key the same way the corpus lane does
  const selection = { programs: ["p1"], handles: {}, rows: [] }
  const corpus = { scopeKey: scope, programs: [{ name: "p1", type: { answer: "number", error: "never", requires: [{ name: 8, service: 4, shape: "number" }] } }] }
  const [q] = queriesFromInputs(repo, selection, corpus, [])
  expect(q?.expected.R).toBe("(number)")
  expect(q?.inputIssues).toEqual([])
})

test("handle targets are bound by declaration, and structured types preserve nesting", () => {
  // The rendered text is pasted verbatim; the binding is a declaration the compiler resolves,
  // so a literal that spells a handle name is untouched (it is not a type reference).
  expect(bindingSource({ "Host.Resource": "Adapter.HostResource" }))
    .toEqual(["declare namespace Host { export type Resource = Adapter.HostResource }"])
  expect(bindingSource({ Resource: "Adapter.HostResource" })).toEqual(["type Resource = Adapter.HostResource"])
  expect(bindingSource({ "A.B.C": "X.Y", "A.D": "Z" }))
    .toEqual(["declare namespace A { export namespace B { export type C = X.Y } export type D = Z }"])
  expect(bindingSource(undefined)).toEqual([])
  expect(() => bindingSource({ "Host.Resource": "not a type" })).toThrow("qualified target")
  expect(() => bindingSource({ "Host-Resource": "Adapter.HostResource" })).toThrow("binding name")
  expect(() => bindingSource({ "A.B": "X", "C.D": "X" })).toThrow("noninjective")
  expect(() => bindingSource({ A: "X", "A.B": "Y" })).toThrow("both a name and a namespace")
  // the binding reaches a nested payload because the compiler resolves the name, not a rewrite
  expect(bindingSource(Object.fromEntries(bindings))[0]).toContain("Adapter.HostResource")
})

test("selected IDs cannot vanish with absent metadata and unexpected inventory is refused", () => {
  const selection = JSON.parse(readFileSync(resolve(repo, "Test/fixtures/target/selection.json"), "utf8"))
  const corpus = JSON.parse(readFileSync(resolve(repo, "harness/truth/corpus.json"), "utf8"))
  const programIds = corpus.programs.map((entry: { name: string }) => `program/${entry.name}`)
  const rowIds = selection.rows.map((row: { table: string; name: string }) => `row/${row.table}/${row.name}`)
  const queries = queriesFromInputs(repo, selection, { programs: [] }, [])
  // Exact identities come from the independent corpus and row selection, not a count pin.
  expect(programIds.length).toBeGreaterThan(0)
  expect(queries.map(q => q.id)).toEqual([...programIds, ...rowIds])
  expect(new Set(queries.map(q => q.id)).size).toBe(queries.length)
  expect(queries.filter(q => q.id.startsWith("program/")).every(q => q.kind === "program")).toBe(true)
  expect(queries.filter(q => q.id.startsWith("row/")).every(q => q.kind === "function")).toBe(true)
  expect(queries.every(q => q.inputIssues?.length)).toBe(true)
  expect(queries.filter(q => q.id.startsWith("row/")).every(q => q.inputIssues?.some(i => i.code === "row-type-metadata"))).toBe(true)
  const minimal = { programs: ["p42"], handles: {}, rows: [] }
  const extra = queriesFromInputs(repo, minimal, { scopeKey: { name: 7, service: 2 }, programs: [{ name: "p42", type: { answer: "number", error: "never", requires: [] } }, { name: "notSelected" }] }, [])
  expect(extra[0]?.inputIssues?.some(i => i.code === "program-inventory")).toBe(true)
})
