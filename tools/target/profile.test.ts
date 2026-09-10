import { expect, test } from "bun:test"
import { resolve } from "node:path"
import { readFileSync } from "node:fs"
import { bindRendered, key, queriesFromInputs, renderTy, requirements, rowArguments, receiverOfSubject } from "./profile.ts"
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
  expect(receiverOfSubject('Adapter.SqlHandle["unsafe"]')).toBe("Adapter.SqlHandle")
  expect(receiverOfSubject('Adapter.KvHandle["get"]')).toBe("Adapter.KvHandle")
  expect(receiverOfSubject("typeof Adapter.Host.acquire")).toBeUndefined()
  expect(() => rowArguments({ ...row, typeArgs: ["number"] }, bindings)).toThrow("unsupported")
})

test("full requirement keys have explicit, bounded and injective target bindings", () => {
  const scope = { name: 7, service: 2 }
  expect(requirements([], scope)).toBe("never")
  expect(requirements([scope], scope)).toBe("(Scope.Scope)")
  expect(() => requirements([{ name: 8, service: 2 }], scope)).toThrow("unbound")
  expect(() => requirements(undefined, scope)).toThrow("full requires")
  expect(() => key({ name: Number.MAX_SAFE_INTEGER + 1, service: 2 })).toThrow("safe natural")
  expect(() => key({ name: -1, service: 2 })).toThrow("safe natural")
  expect(() => requirements([{ name: 1, service: 3 }, { name: 2, service: 3 }], scope, new Map([["1:3", "C.Service"], ["2:3", "C.Service"]]))).toThrow("noninjective")
})

test("rendered canonical type bindings use syntax nodes and structured types preserve nesting", () => {
  const bound = bindRendered('readonly [Host.Resource, "Host.Resource"]', bindings)
  expect(bound).toContain("Adapter.HostResource")
  expect(bound).toContain('"Host.Resource"')
  expect(bound).not.toContain('"Adapter.HostResource"')
  expect(() => bindRendered("number |", bindings)).toThrow("syntax")
  expect(() => bindRendered("number; type Extra = string", bindings)).toThrow("expression")
  expect(renderTy({ _tag: "option", inner: { _tag: "list", inner: { _tag: "handle", target: "Host.Resource" } } }, bindings)).toBe("Option.Option<ReadonlyArray<Adapter.HostResource>>")
  expect(() => renderTy({ _tag: "handle", target: "Missing.Handle" }, bindings)).toThrow("unbound")
})

test("selected IDs cannot vanish with absent metadata and unexpected inventory is refused", () => {
  const selection: unknown = JSON.parse(readFileSync(resolve(repo, "Test/fixtures/target/selection.json"), "utf8"))
  const queries = queriesFromInputs(repo, selection, { programs: [] }, [])
  expect(queries).toHaveLength(35)
  expect(new Set(queries.map(q => q.id)).size).toBe(35)
  expect(queries.filter(q => q.id.startsWith("program/"))).toHaveLength(24)
  expect(queries.every(q => q.inputIssues?.length)).toBe(true)
  expect(queries.filter(q => q.id.startsWith("row/")).every(q => q.inputIssues?.some(i => i.code === "row-type-metadata"))).toBe(true)
  const minimal = { programs: ["p42"], handles: {}, rows: [] }
  const extra = queriesFromInputs(repo, minimal, { scopeKey: { name: 7, service: 2 }, programs: [{ name: "p42", type: { answer: "number", error: "never", requires: [] } }, { name: "notSelected" }] }, [])
  expect(extra[0]?.inputIssues?.some(i => i.code === "program-inventory")).toBe(true)
})
