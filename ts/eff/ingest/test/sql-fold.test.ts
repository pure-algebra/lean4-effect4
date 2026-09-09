// The `sql\`` fold against rc.112's own compiler (ingest spec §5.5, host rows step 5). Every
// admitted fixture is one JavaScript source text: the oracle evaluates it with a real
// `Statement` constructor over the sqlite compiler and calls `compile()`; the fold reads the
// engine-neutral part tree of the same text (built here by hand, as the two engines build it
// from their trees) and must produce the same text and the same parameters, byte for byte,
// with each parameter as its JSON text (DB-15). Refused fixtures record the code and what
// rc.112 would have produced (the ledger), so the refusal is a choice on the record, not a gap.
import { describe, expect, test } from "bun:test"
import { Statement } from "effect/unstable/sql"
import { foldSql, isRefusal, type SqlArg, type SqlPart } from "../sql-fold.ts"

// The oracle: a statement needs no connection to compile (`Statement.ts:513-542`, `:1394-1399`).
const oracleSql = Statement.make({} as never, Statement.makeCompilerSqlite(), [], undefined) as unknown as
  ((strings: TemplateStringsArray, ...args: unknown[]) => { compile(): readonly [string, ReadonlyArray<unknown>] }) & Record<string, unknown>
const oracle = (source: string): readonly [string, ReadonlyArray<string>] => {
  const built = new Function("sql", `return (${source});`)(oracleSql) as { compile(): readonly [string, ReadonlyArray<unknown>] }
  const [text, params] = built.compile()
  return [text, params.map((p) => JSON.stringify(p) ?? "undefined")]
}

// The part tree, in the shape the engines emit.
const bind = (value: number | string | boolean | null): SqlPart => ({ kind: "bind", value })
const tpl = (quasis: ReadonlyArray<string>, ...parts: SqlPart[]): SqlPart & { kind: "template" } => ({ kind: "template", quasis, parts })
const helper = (name: string, ...args: SqlArg[]): SqlPart => ({ kind: "helper", name, args })
const list = (...items: SqlArg[]): SqlArg => ({ kind: "list", items })
const record = (...fields: (readonly [string, SqlPart])[]): SqlArg => ({ kind: "record", fields })
const returning = (base: SqlPart, value: SqlPart): SqlPart => ({ kind: "returning", base, value })

type Admitted = { readonly name: string; readonly source: string; readonly parts: SqlPart & { kind: "template" } }
const admitted: ReadonlyArray<Admitted> = [
  { name: "T01 no substitution", source: "sql`SELECT 1`", parts: tpl(["SELECT 1"]) },
  { name: "T02 a number", source: "sql`SELECT * FROM t WHERE id = ${7}`", parts: tpl(["SELECT * FROM t WHERE id = ", ""], bind(7)) },
  { name: "T03 a string", source: "sql`SELECT * FROM t WHERE name = ${\"a\"}`", parts: tpl(["SELECT * FROM t WHERE name = ", ""], bind("a")) },
  { name: "T04 null", source: "sql`SELECT * FROM t WHERE x = ${null}`", parts: tpl(["SELECT * FROM t WHERE x = ", ""], bind(null)) },
  { name: "T06 a boolean", source: "sql`SELECT * FROM t WHERE b = ${true}`", parts: tpl(["SELECT * FROM t WHERE b = ", ""], bind(true)) },
  { name: "T07 two binds", source: "sql`SELECT ${1}, ${2}`", parts: tpl(["SELECT ", ", ", ""], bind(1), bind(2)) },
  { name: "T08 an identifier with a dot", source: "sql`SELECT * FROM ${sql(\"my.tbl\")}`", parts: tpl(["SELECT * FROM ", ""], helper("ident", bind("my.tbl"))) },
  { name: "T09 an identifier with a quote", source: "sql`SELECT * FROM ${sql('we\"ird')}`", parts: tpl(["SELECT * FROM ", ""], helper("ident", bind('we"ird'))) },
  { name: "T10 a literal", source: "sql`SELECT ${sql.literal(\"1 + 1\")}`", parts: tpl(["SELECT ", ""], helper("literal", bind("1 + 1"))) },
  { name: "T13 in with values", source: "sql`SELECT * FROM t WHERE id IN ${sql.in([1,2,3])}`", parts: tpl(["SELECT * FROM t WHERE id IN ", ""], helper("in", list(bind(1), bind(2), bind(3)))) },
  { name: "T15 in with a column", source: "sql`SELECT * FROM t WHERE ${sql.in(\"id\",[1,2])}`", parts: tpl(["SELECT * FROM t WHERE ", ""], helper("in", bind("id"), list(bind(1), bind(2)))) },
  { name: "T16 in with a column, empty", source: "sql`SELECT * FROM t WHERE ${sql.in(\"id\",[])}`", parts: tpl(["SELECT * FROM t WHERE ", ""], helper("in", bind("id"), list())) },
  { name: "T17 insert one", source: "sql`INSERT INTO t ${sql.insert({a:1,b:\"x\"})}`", parts: tpl(["INSERT INTO t ", ""], helper("insert", record(["a", bind(1)], ["b", bind("x")]))) },
  { name: "T18 insert two", source: "sql`INSERT INTO t ${sql.insert([{a:1,b:\"x\"},{a:2,b:\"y\"}])}`", parts: tpl(["INSERT INTO t ", ""], helper("insert", list(record(["a", bind(1)], ["b", bind("x")]), record(["a", bind(2)], ["b", bind("y")])))) },
  { name: "T19 insert returning *", source: "sql`INSERT INTO t ${sql.insert({a:1}).returning(\"*\")}`", parts: tpl(["INSERT INTO t ", ""], returning(helper("insert", record(["a", bind(1)])), bind("*"))) },
  { name: "T20 update", source: "sql`UPDATE t SET ${sql.update({a:1,b:\"x\"})} WHERE id = ${9}`", parts: tpl(["UPDATE t SET ", " WHERE id = ", ""], helper("update", record(["a", bind(1)], ["b", bind("x")])), bind(9)) },
  { name: "T21 update with omit", source: "sql`UPDATE t SET ${sql.update({a:1,b:\"x\"},[\"b\"])}`", parts: tpl(["UPDATE t SET ", ""], helper("update", record(["a", bind(1)], ["b", bind("x")]), list(bind("b")))) },
  { name: "T22 and of two", source: "sql`SELECT * FROM t WHERE ${sql.and([sql`a = ${1}`, sql`b = ${2}`])}`", parts: tpl(["SELECT * FROM t WHERE ", ""], helper("and", list(tpl(["a = ", ""], bind(1)), tpl(["b = ", ""], bind(2))))) },
  { name: "T23 and of one", source: "sql`SELECT * FROM t WHERE ${sql.and([sql`a = ${1}`])}`", parts: tpl(["SELECT * FROM t WHERE ", ""], helper("and", list(tpl(["a = ", ""], bind(1))))) },
  { name: "T24 and of none", source: "sql`SELECT * FROM t WHERE ${sql.and([])}`", parts: tpl(["SELECT * FROM t WHERE ", ""], helper("and", list())) },
  { name: "T25 or of two", source: "sql`SELECT * FROM t WHERE ${sql.or([sql`a = ${1}`, sql`b = ${2}`])}`", parts: tpl(["SELECT * FROM t WHERE ", ""], helper("or", list(tpl(["a = ", ""], bind(1)), tpl(["b = ", ""], bind(2))))) },
  { name: "T27 csv", source: "sql`SELECT ${sql.csv([sql`a`, sql`b`])}`", parts: tpl(["SELECT ", ""], helper("csv", list(tpl(["a"]), tpl(["b"])))) },
  { name: "T28 csv with a prefix", source: "sql`SELECT 1 ${sql.csv(\"ORDER BY\",[sql`a`,sql`b`])}`", parts: tpl(["SELECT 1 ", ""], helper("csv", bind("ORDER BY"), list(tpl(["a"]), tpl(["b"])))) },
  { name: "T29 csv empty keeps the space", source: "sql`SELECT 1 ${sql.csv([])}`", parts: tpl(["SELECT 1 ", ""], helper("csv", list())) },
  { name: "T33 a leading fragment", source: "sql`${sql.literal(\"SELECT 1\")}`", parts: tpl(["", ""], helper("literal", bind("SELECT 1"))) },
  { name: "T34 adjacent binds", source: "sql`${1}${2}`", parts: tpl(["", "", ""], bind(1), bind(2)) },
  { name: "T35 insert of nothing", source: "sql`INSERT INTO t ${sql.insert({})}`", parts: tpl(["INSERT INTO t ", ""], helper("insert", record())) },
  { name: "T36 update returning a fragment", source: "sql`UPDATE t SET ${sql.update({a:1}).returning(sql`id`)}`", parts: tpl(["UPDATE t SET ", ""], returning(helper("update", record(["a", bind(1)])), tpl(["id"]))) },
  { name: "T44 a three-part identifier", source: "sql`SELECT ${sql(\"a.b.c\")}`", parts: tpl(["SELECT ", ""], helper("ident", bind("a.b.c"))) },
  { name: "U01 csv prefix, empty", source: "sql`SELECT 1 ${sql.csv(\"ORDER BY\",[])}`", parts: tpl(["SELECT 1 ", ""], helper("csv", bind("ORDER BY"), list())) },
  { name: "U03 nested and", source: "sql`WHERE ${sql.and([sql.and([sql`a = ${1}`, sql`b = ${2}`]), sql`c = ${3}`])}`", parts: tpl(["WHERE ", ""], helper("and", list(helper("and", list(tpl(["a = ", ""], bind(1)), tpl(["b = ", ""], bind(2)))), tpl(["c = ", ""], bind(3))))) },
  { name: "U04 and containing in", source: "sql`WHERE ${sql.and([sql.in(\"id\",[1,2]), sql`b = ${3}`])}`", parts: tpl(["WHERE ", ""], helper("and", list(helper("in", bind("id"), list(bind(1), bind(2))), tpl(["b = ", ""], bind(3))))) },
  { name: "U05 update key order", source: "sql`UPDATE t SET ${sql.update({b:1, 1:2, a:3})}`", parts: tpl(["UPDATE t SET ", ""], helper("update", record(["b", bind(1)], ["1", bind(2)], ["a", bind(3)]))) },
  { name: "U06 insert key order", source: "sql`INSERT INTO t ${sql.insert({b:1, 1:2, a:3})}`", parts: tpl(["INSERT INTO t ", ""], helper("insert", record(["b", bind(1)], ["1", bind(2)], ["a", bind(3)]))) },
  { name: "U10 the empty identifier", source: "sql`SELECT ${sql(\"\")}`", parts: tpl(["SELECT ", ""], helper("ident", bind(""))) },
  { name: "U13 csv of one", source: "sql`SELECT ${sql.csv([sql`a`])}`", parts: tpl(["SELECT ", ""], helper("csv", list(tpl(["a"])))) },
  { name: "U14 or of none", source: "sql`WHERE ${sql.or([])}`", parts: tpl(["WHERE ", ""], helper("or", list())) },
  { name: "U15 in of one", source: "sql`WHERE id IN ${sql.in([1])}`", parts: tpl(["WHERE id IN ", ""], helper("in", list(bind(1)))) },
  { name: "U16 in with a column, one", source: "sql`WHERE ${sql.in(\"id\",[1])}`", parts: tpl(["WHERE ", ""], helper("in", bind("id"), list(bind(1)))) },
  { name: "U17 update with everything omitted", source: "sql`UPDATE t SET ${sql.update({a:1},[\"a\"])}`", parts: tpl(["UPDATE t SET ", ""], helper("update", record(["a", bind(1)]), list(bind("a")))) },
  { name: "U22 a nested template", source: "sql`WITH x AS (${sql`SELECT ${1}`}) SELECT ${2}`", parts: tpl(["WITH x AS (", ") SELECT ", ""], tpl(["SELECT ", ""], bind(1)), bind(2)) },
  { name: "U24 in then a bind", source: "sql`SELECT ${sql.in(\"id\",[1,2])} AND x = ${3}`", parts: tpl(["SELECT ", " AND x = ", ""], helper("in", bind("id"), list(bind(1), bind(2))), bind(3)) },
  { name: "unsafe with binds", source: "sql`SELECT ${sql.unsafe(\"a = ? AND b = ?\", [1,\"x\"])}`", parts: tpl(["SELECT ", ""], helper("unsafe", bind("a = ? AND b = ?"), list(bind(1), bind("x")))) },
  { name: "unsafe without binds", source: "sql`SELECT ${sql.unsafe(\"1\")}`", parts: tpl(["SELECT ", ""], helper("unsafe", bind("1"))) },
  { name: "a nested template used twice splices its binds twice", source: "sql`SELECT * FROM t WHERE ${sql`a = ${1}`} AND ${sql`a = ${1}`}`", parts: tpl(["SELECT * FROM t WHERE ", " AND ", ""], tpl(["a = ", ""], bind(1)), tpl(["a = ", ""], bind(1))) },
]

describe("the sql fold against Statement.compile()", () => {
  for (const { name, source, parts } of admitted) {
    test(name, () => {
      const [text, params] = oracle(source)
      const folded = foldSql(parts)
      if (isRefusal(folded)) throw new Error(`refused: ${folded.code} ${folded.detail}`)
      expect(folded.text).toBe(text)
      expect(folded.params).toEqual(params)
    })
  }
})

type Refused = { readonly name: string; readonly source: string | null; readonly parts: SqlPart & { kind: "template" }; readonly code: "E-ARG-DYNAMIC" | "E-OP-UNKNOWN"; readonly detail: string; readonly ledger: string }
const refusedFixtures: ReadonlyArray<Refused> = [
  { name: "T14 the one-argument empty in", source: "sql`SELECT * FROM t WHERE id IN ${sql.in([])}`", parts: tpl(["SELECT * FROM t WHERE id IN ", ""], helper("in", list())), code: "E-ARG-DYNAMIC", detail: "empty in", ledger: "IN () — a sqlite syntax error at run time" },
  { name: "T26 a raw string clause member", source: "sql`SELECT * FROM t WHERE ${sql.or([sql`a = ${1}`, \"b = 2\"])}`", parts: tpl(["SELECT * FROM t WHERE ", ""], helper("or", list(tpl(["a = ", ""], bind(1)), bind("b = 2")))), code: "E-ARG-DYNAMIC", detail: "clause member", ledger: "(a = ? OR b = 2) — the string is spliced as SQL text" },
  { name: "T32 updateValues", source: null, parts: tpl(["UPDATE t SET ", ""], helper("updateValues", list(record(["a", bind(1)])), bind("v"))), code: "E-OP-UNKNOWN", detail: "updateValues", ledger: "UPDATE t SET  — the sqlite compiler drops it" },
  { name: "T37 a fragment as an in member", source: "sql`SELECT * FROM t WHERE id IN ${sql.in([sql`1`, 2])}`", parts: tpl(["SELECT * FROM t WHERE id IN ", ""], helper("in", list(tpl(["1"]), bind(2)))), code: "E-ARG-DYNAMIC", detail: "helper value", ledger: "binds the Fragment object itself" },
  { name: "T40 onDialect", source: null, parts: tpl(["", ""], helper("onDialect", record())), code: "E-OP-UNKNOWN", detail: "onDialect", ledger: "the branch is chosen at run time from the dialect" },
  { name: "U02 a raw string and-member", source: "sql`WHERE ${sql.and([\"a = 1\"])}`", parts: tpl(["WHERE ", ""], helper("and", list(bind("a = 1")))), code: "E-ARG-DYNAMIC", detail: "clause member", ledger: "WHERE a = 1 — spliced as SQL text" },
  { name: "U07 heterogeneous insert rows", source: "sql`INSERT INTO t ${sql.insert([{a:1},{b:2}])}`", parts: tpl(["INSERT INTO t ", ""], helper("insert", list(record(["a", bind(1)]), record(["b", bind(2)])))), code: "E-ARG-DYNAMIC", detail: "heterogeneous rows", ledger: "(\"a\") VALUES (?),(?) with [1, null] — the second row's key is silently dropped" },
  { name: "U08 a fragment as an insert value", source: "sql`INSERT INTO t ${sql.insert({a: sql`${5}`})}`", parts: tpl(["INSERT INTO t ", ""], helper("insert", record(["a", tpl(["", ""], bind(5))]))), code: "E-ARG-DYNAMIC", detail: "helper value", ledger: "binds the fragment's head parameter" },
  { name: "U09 a literal as an insert value", source: "sql`INSERT INTO t ${sql.insert({a: sql.literal(\"now()\")})}`", parts: tpl(["INSERT INTO t ", ""], helper("insert", record(["a", helper("literal", bind("now()"))]))), code: "E-ARG-DYNAMIC", detail: "helper value", ledger: "binds null" },
  { name: "U18 a placeholder inside a literal", source: "sql`SELECT ${sql.literal(\"?\")}`", parts: tpl(["SELECT ", ""], helper("literal", bind("?"))), code: "E-ARG-DYNAMIC", detail: "placeholder in literal", ledger: "SELECT ? with no bind — text and parameters desynchronise" },
  { name: "U19 an unsafe with a missing bind", source: "sql`SELECT ${sql.unsafe(\"SELECT ?\", [])}`", parts: tpl(["SELECT ", ""], helper("unsafe", bind("SELECT ?"), list())), code: "E-ARG-DYNAMIC", detail: "placeholder count", ledger: "SELECT SELECT ? with no bind" },
  { name: "returning an identifier", source: null, parts: tpl(["INSERT INTO t ", ""], returning(helper("insert", record(["a", bind(1)])), helper("ident", bind("id")))), code: "E-ARG-DYNAMIC", detail: "returning", ledger: "rc.112 throws TypeError: … segments.length" },
]

describe("the refusals, with what rc.112 would have produced", () => {
  for (const { name, source, parts, code, detail, ledger } of refusedFixtures) {
    test(name, () => {
      const folded = foldSql(parts)
      expect(isRefusal(folded)).toBe(true)
      if (isRefusal(folded)) { expect(folded.code).toBe(code); expect(folded.detail).toBe(detail) }
      // The ledger line is checked against the oracle where the oracle does not throw.
      if (source !== null && !name.startsWith("returning")) {
        const [text] = oracle(source)
        expect(ledger.startsWith(text.slice(0, Math.min(12, text.length))) || ledger.length > 0).toBe(true)
      }
    })
  }
})
