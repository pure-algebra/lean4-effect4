// The canonical package tables on the foreign face (host rows step 5, spec §5.5 "Package rows"
// and §5.9 "Package keys"): both engines resolve a package's key through the `effect` import,
// read a member call on its binder as the table's method row with the receiver paired in
// front of the arguments, carry a bind-parameter array literal as JSON text through `strings`,
// and refuse a member the table does not carry as `E-OP-UNKNOWN` (decision 13). Every case is
// checked on both engines and for their agreement.
import { expect, test } from "bun:test"
import { recognizeSource as ck } from "../ck.ts"
import { recognizeSource as oxc } from "../oxc.ts"
import { compareVerdicts } from "../gate.ts"
import { packageTable } from "../package-rows.ts"
import type { RefusalCode, Verdict } from "../contract.ts"

const header = 'import { Effect, Context } from "effect"; import { SqlClient } from "effect/unstable/sql"; import { KeyValueStore } from "effect/unstable/persistence"; '
const both = (source: string, file: string): readonly [readonly Verdict[], readonly Verdict[]] => {
  const left = ck(source, file), right = oxc(source, file)
  expect(compareVerdicts(left, right).status).toBe("agree")
  return [left, right]
}
const lifted = (v: Verdict | undefined) => {
  expect(v?.kind).toBe("lifted")
  if (v?.kind !== "lifted") throw new Error("expected a lifted verdict")
  return v
}
const refused = (v: Verdict | undefined, code: RefusalCode, detail: string) => {
  expect(v?.kind).toBe("refusal")
  if (v?.kind === "refusal") { expect(v.code).toBe(code); expect(v.detail).toContain(detail) }
}
// Expected shapes are built as plain data (`unknown`), compared structurally against the
// decoded `Eff`; the schema decode on the engines' side is what types them.
const index = (spelling: string): number => packageTable.findIndex(r => r.spelling === spelling)
const v = (i: number): unknown => ({ _tag: "var", index: i })
const str = (value: string): unknown => ({ _tag: "lit", value: { _tag: "str", value } })
const pair = (a: unknown, b: unknown): unknown => ({ _tag: "app", atom: "pair", args: [a, b] })
const strings = (...texts: string[]): unknown => ({ _tag: "app", atom: "strings", args: texts.map(str) })
const external = (spelling: string, request: unknown): unknown => ({ _tag: "callback", register: { _tag: "external", index: index(spelling) }, request })
const sqlKey: unknown = { name: { value: 4 }, service: { value: 8 } }
const kvKey: unknown = { name: { value: 4 }, service: { value: 9 } }

test("the canonical table is both packages' rows in package order", () => {
  expect(packageTable.map(r => r.spelling)).toEqual(["Sql.open", "unsafe", "Sql.close", "Kv.make", "get", "set", "remove", "has"])
})

test("a package key is its service, and a member call on its binder is the table's method row", () => {
  const source = header + 'const p = Effect.gen(function* () { const sql = yield* SqlClient.SqlClient; const rows = yield* sql.unsafe("SELECT 1", []); return rows; });'
  for (const result of both(source, "sql.ts")) {
    expect(result).toHaveLength(1)
    const w = lifted(result[0])
    expect(w.keys).toEqual([{ ordinal: 4, service: 8, sourceId: "effect/sql/SqlClient" }])
    expect(w.eff as unknown).toEqual({ _tag: "gen", body: [
      { _tag: "bindYield", effect: { _tag: "service", key: sqlKey } },
      { _tag: "bindYield", effect: external("unsafe", pair(v(0), pair(str("SELECT 1"), strings()))) },
      { _tag: "ret", value: v(1) },
    ] })
  }
})

test("bind parameters cross as JSON text through strings; an omitted optional list is empty", () => {
  const source = header + 'const p = Effect.gen(function* () { const sql = yield* SqlClient.SqlClient; const a = yield* sql.unsafe("INSERT INTO t VALUES (?, ?, ?, ?)", [7, "x", true, null]); const b = yield* sql.unsafe("SELECT 1"); return b; });'
  for (const result of both(source, "binds.ts")) {
    const w = lifted(result[0])
    if (w.eff._tag !== "gen") throw new Error("expected gen")
    expect(w.eff.body[1] as unknown).toEqual({ _tag: "bindYield", effect: external("unsafe", pair(v(0), pair(str("INSERT INTO t VALUES (?, ?, ?, ?)"), strings("7", "\"x\"", "true", "null")))) })
    expect(w.eff.body[2] as unknown).toEqual({ _tag: "bindYield", effect: external("unsafe", pair(v(0), pair(str("SELECT 1"), strings()))) })
  }
})

test("a bind outside the literal alphabet is a dynamic argument", () => {
  const source = header + 'const p = Effect.gen(function* () { const sql = yield* SqlClient.SqlClient; const n = yield* Effect.succeed(1); const r = yield* sql.unsafe("SELECT ?", [n]); return r; });'
  for (const result of both(source, "dynamic-bind.ts")) refused(result[0], "E-ARG-DYNAMIC", "bind")
})

test("a member the table does not carry is an unknown head on both engines (decision 13)", () => {
  for (const [call, member] of [
    ["sql.withTransaction(Effect.succeed(1))", "withTransaction"],
    ['sql.execute("SELECT 1", [])', "execute"],
    ["sql.reserve", "reserve"],
  ] as const) {
    const source = header + `const p = Effect.gen(function* () { const sql = yield* SqlClient.SqlClient; const r = yield* ${call}; return r; });`
    for (const result of both(source, `unknown-${member}.ts`)) refused(result[0], "E-OP-UNKNOWN", member)
  }
})

test("a receiver that is not a binder is an unresolved receiver", () => {
  const source = header + 'const p = Effect.gen(function* () { const rows = yield* sql.unsafe("SELECT 1", []); return rows; });'
  for (const result of both(source, "unbound-receiver.ts")) refused(result[0], "E-OP-RECEIVER", "sql.unsafe")
})

test("the key-value store: make is not foreign, the methods are, get answers under the row", () => {
  const source = header + 'const p = Effect.gen(function* () { const store = yield* KeyValueStore.KeyValueStore; yield* store.set("k", "1"); const seen = yield* store.get("k"); return seen; });'
  for (const result of both(source, "kv.ts")) {
    const w = lifted(result[0])
    expect(w.keys).toEqual([{ ordinal: 4, service: 9, sourceId: "effect/persistence/KeyValueStore" }])
    expect(w.eff as unknown).toEqual({ _tag: "gen", body: [
      { _tag: "bindYield", effect: { _tag: "service", key: kvKey } },
      { _tag: "yieldDiscard", effect: external("set", pair(v(0), pair(str("k"), str("1")))) },
      { _tag: "bindYield", effect: external("get", pair(v(0), str("k"))) },
      { _tag: "ret", value: v(1) },
    ] })
  }
})

test("Effect.service on a package key, and a declared key of a package shape (codes 8 and 9)", () => {
  const source = header + 'const p = Effect.service(SqlClient.SqlClient); const Db = Context.Service<SqlClient.SqlClient>("Db"); const q = Effect.service(Db); const Store = Context.Service<KeyValueStore.KeyValueStore>("Store"); const r = Effect.service(Store);'
  for (const result of both(source, "keys.ts")) {
    expect(result.map(w => w.unit.name)).toEqual(["p", "q", "r"])
    expect(lifted(result[0]).eff as unknown).toEqual({ _tag: "service", key: sqlKey })
    expect(lifted(result[0]).keys).toEqual([{ ordinal: 4, service: 8, sourceId: "effect/sql/SqlClient" }])
    expect(lifted(result[1]).keys).toEqual([{ ordinal: 4, service: 8, sourceId: "Db" }])
    expect(lifted(result[2]).keys).toEqual([{ ordinal: 4, service: 9, sourceId: "Store" }])
  }
})

test("package keys take first-use ordinals beside declared keys", () => {
  const source = header + 'const K = Context.Service<number>("K"); const p = Effect.gen(function* () { const n = yield* Effect.service(K); const sql = yield* SqlClient.SqlClient; const r = yield* sql.unsafe("SELECT 1", []); return r; });'
  for (const result of both(source, "ordinals.ts")) {
    expect(lifted(result[0]).keys).toEqual([{ ordinal: 4, service: 4, sourceId: "K" }, { ordinal: 5, service: 8, sourceId: "effect/sql/SqlClient" }])
  }
})
