import { expect, test } from "bun:test"
import { resolve } from "node:path"
import { readFileSync } from "node:fs"
import { key, queriesFromInputs, renderTy, requirements, rowArguments, receiverOfSubject } from "./profile.ts"
import { bindingSource } from "./oracle.ts"
import type { Row } from "../../ts/eff/eff.gen.ts"

const repo = resolve(import.meta.dir, "../..")
const bindings = new Map([["Host.Resource", "Adapter.HostResource"]])
const row: Row = { name: "control", spelling: "Control.call", shape: "call", trailing: [], typeArgs: [], kind: "async", registration: "external", cite: "independent control",
  request: { _tag: "prod", left: { _tag: "string" }, right: { _tag: "prod", left: { _tag: "nat" }, right: { _tag: "bool" } } },
  answer: { _tag: "unit" }, error: { _tag: "never" }, requires: [] }

test("request projection follows call shape and splits only one tuple level", () => {
  expect(rowArguments(row, bindings)).toEqual({ request: "[readonly [string, readonly [number, boolean]]]" })
  expect(rowArguments({ ...row, shape: "tupleCall" }, bindings)).toEqual({ request: "[string, readonly [number, boolean]]" })
  expect(rowArguments({ ...row, shape: "method" }, bindings)).toEqual({ receiver: "string", request: "[number, boolean]" })
  expect(rowArguments({ ...row, request: { _tag: "unit" } }, bindings)).toEqual({ request: "[]" })
  expect(() => rowArguments({ ...row, shape: "value" }, bindings)).toThrow("not a callable")
  expect(() => rowArguments({ ...row, shape: "method", request: { _tag: "string" } }, bindings)).toThrow("receiver")
  expect(() => rowArguments({ ...row, trailing: ["undefined"] }, bindings)).toThrow("unsupported")
  expect(() => rowArguments({ ...row, shape: "tupleCall", request: { _tag: "unit" } }, bindings)).toThrow("binary product")
  expect(() => rowArguments({ ...row, typeArgs: ["number"] }, bindings)).toThrow("unsupported")
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
  expect(renderTy({ _tag: "option", inner: { _tag: "list", inner: { _tag: "handle", target: "Host.Resource" } } }, bindings)).toBe("Option.Option<ReadonlyArray<Adapter.HostResource>>")
  expect(renderTy({ _tag: "lit", value: 'A"B' }, bindings)).toBe('"A\\"B"')
  expect(() => renderTy({ _tag: "handle", target: "Missing.Handle" }, bindings)).toThrow("unbound")
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
