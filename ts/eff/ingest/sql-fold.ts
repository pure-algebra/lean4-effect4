// The `sql\`` derived form (ingest spec §5.5, host rows step 5): the static fold of a tagged
// template under the sqlite dialect into the `unsafe` row's `(text, params)`. rc.112 owns the
// lowering — `Statement.compile()` (vendor/effect-4.0.0-rc.112/src/unstable/sql/Statement.ts:
// `statement()` :616-643 builds the segments, `CompilerProto.compile` :833-1055 folds them,
// `makeCompilerSqlite` :1074-1090 is the dialect) — and every admitted case is checked against
// it byte for byte by `test/sql-fold.test.ts`. The fold is engine-neutral: each engine converts
// its own tree into `SqlPart` (the syntactic part) and this module computes the pair or the
// refusal (the semantic part), so the two engines cannot disagree on a lowering.
//
// Admitted (each restates a `Statement.ts` arm): quasis as text; a bind literal (a canonical
// non-negative integer, a string, a boolean, `null`) as `?` plus its JSON text (DB-15); a
// nested template, spliced by value at each use; `sql(name)` as the escaped identifier;
// `sql.literal(text)` as text without `?`; `sql.unsafe(text, [binds])` as text whose `?` count
// is its bind count; `sql.in([v…])` and `sql.in(col, [v…])` with a literal column, the empty
// two-argument form `1=0`; `sql.insert(record | [records])` and `sql.update(record, [omit…])`
// with literal keys in JavaScript key order; `sql.and`/`or` (`1=1` when empty, no brackets
// around one clause) and `sql.csv` / `sql.csv(prefix, …)` (the empty fragment when empty) over
// fragment members; `.returning(text | template)` on an insert or update.
//
// Refused, with the taxonomy code (the ledger in `test/sql-fold.test.ts` records what rc.112
// would have produced): a bind outside the alphabet, `undefined`, a variable, a `Date`, an
// array, an object, a bigint (`E-ARG-DYNAMIC` "bind"); the one-argument `sql.in([])`, which
// compiles to the syntax error `IN ()` (`E-ARG-DYNAMIC` "empty in"); a raw string member of a
// clause helper, which is spliced as SQL text (`E-ARG-DYNAMIC` "clause member"); a non-literal
// identifier, key, prefix or omit list (`E-ARG-DYNAMIC`); heterogeneous insert rows; `?` in a
// literal or a bind-count mismatch in `unsafe` (`E-ARG-DYNAMIC` "placeholder"); a fragment or
// helper as an insert/update value or an `in` member (`E-ARG-DYNAMIC` "helper value");
// `.returning(sql(name))`, which throws in rc.112; `updateValues`, `onDialect`,
// `onDialectOrElse`, `join`, a `Custom` segment and any other member (`E-OP-UNKNOWN`).

export type Bind = number | string | boolean | null

export type SqlPart =
  | { readonly kind: "bind"; readonly value: Bind }
  | { readonly kind: "template"; readonly quasis: ReadonlyArray<string>; readonly parts: ReadonlyArray<SqlPart> }
  | { readonly kind: "helper"; readonly name: string; readonly args: ReadonlyArray<SqlArg> }
  | { readonly kind: "returning"; readonly base: SqlPart; readonly value: SqlPart }
  | { readonly kind: "dynamic"; readonly detail: string }

export type SqlArg =
  | SqlPart
  | { readonly kind: "list"; readonly items: ReadonlyArray<SqlArg> }
  | { readonly kind: "record"; readonly fields: ReadonlyArray<readonly [string, SqlPart]> }

export type Folded = { readonly text: string; readonly params: ReadonlyArray<string> }
export type SqlRefusal = { readonly code: "E-ARG-DYNAMIC" | "E-OP-UNKNOWN"; readonly detail: string }

class Refused extends Error {
  constructor(readonly refusal: SqlRefusal) { super(refusal.code) }
}
const dynamic = (detail: string): never => { throw new Refused({ code: "E-ARG-DYNAMIC", detail }) }
const unknown = (detail: string): never => { throw new Refused({ code: "E-OP-UNKNOWN", detail }) }

/** `escapeSqlite = defaultEscape("\"")` (`Statement.ts:1101-1108`, `:1515`): wrap in `"`,
 * double an interior `"`, and spell each `.` as `"."`. */
export const escapeSqlite = (name: string): string => `"${name.replaceAll('"', '""').replaceAll(".", '"."')}"`

/** The JSON text of a bind (DB-15). */
const bindText = (value: Bind): string => {
  if (value === null) return "null"
  if (typeof value === "boolean") return value ? "true" : "false"
  if (typeof value === "number") return Number.isSafeInteger(value) && value >= 0 ? String(value) : dynamic("bind")
  return JSON.stringify(value)
}

/** JavaScript's own key order (`Object.keys`, `Statement.ts:891`): array-index keys first,
 * ascending, then the others in insertion order. */
const keyOrder = (fields: ReadonlyArray<readonly [string, SqlPart]>): ReadonlyArray<string> => {
  const names = fields.map(([k]) => k)
  if (new Set(names).size !== names.length) return dynamic("record key")
  const isIndex = (k: string): boolean => /^(0|[1-9][0-9]*)$/.test(k) && Number(k) < 4294967295
  const indexed = names.filter(isIndex).sort((a, b) => Number(a) - Number(b))
  return [...indexed, ...names.filter((k) => !isIndex(k))]
}

type Segment = { readonly text: string } | { readonly bind: string }

const literalText = (part: SqlArg | undefined, what: string): string => {
  if (part?.kind !== "bind" || typeof part.value !== "string") return dynamic(what)
  return part.value
}

/** A list argument whose items are parts (binds, fragments), never records. */
const requireList = (arg: SqlArg | undefined, what: string): ReadonlyArray<SqlPart> =>
  arg?.kind === "list" ? arg.items.map((item) => item.kind === "list" || item.kind === "record" ? dynamic(what) : item) : dynamic(what)

const requireRecord = (arg: SqlArg | undefined): ReadonlyArray<readonly [string, SqlPart]> =>
  arg?.kind === "record" ? arg.fields : dynamic("record key")

/** A cell of `insert`/`update`: a bind literal only. rc.112's `extractPrimitive` would bind a
 * fragment's head parameter or `null`, which is a corruption, not a lowering. */
const cell = (part: SqlPart): string => part.kind === "bind" ? bindText(part.value) : dynamic("helper value")

const bindsOf = (items: ReadonlyArray<SqlPart>, what: string): ReadonlyArray<string> =>
  items.map((item) => item.kind === "bind" ? bindText(item.value) : dynamic(what))

const placeholders = (text: string): number => text.split("?").length - 1

/** A clause member: a fragment (nested template, a fragment-answering helper, a returning
 * form), never a raw string (which rc.112 splices as SQL text). */
const member = (part: SqlPart): ReadonlyArray<Segment> => {
  if (part.kind === "bind") return dynamic("clause member")
  if (part.kind === "helper" && part.name === "in" && part.args.length === 1) return dynamic("clause member")
  return segmentsOf(part)
}

/** `join(sep, addParens, fallback)` (`Statement.ts:648-682`): the fallback when empty, one
 * member unbracketed, two or more separated and bracketed when the helper brackets. */
const joinFold = (members: ReadonlyArray<SqlPart>, sep: string, parens: boolean, fallback: string): ReadonlyArray<Segment> => {
  if (members.length === 0) return [{ text: fallback }]
  if (members.length === 1) return member(members[0]!)
  const out: Segment[] = parens ? [{ text: "(" }] : []
  members.forEach((m, i) => {
    if (i > 0) out.push({ text: sep })
    out.push(...member(m))
  })
  if (parens) out.push({ text: ")" })
  return out
}

const segmentsOf = (part: SqlPart): ReadonlyArray<Segment> => {
  switch (part.kind) {
    case "bind": return [{ text: "?" }, { bind: bindText(part.value) }]
    case "dynamic": return dynamic(part.detail)
    case "template": {
      // `statement()` (`Statement.ts:616-643`): a quasi contributes text only when non-empty;
      // a nested fragment splices its segments; anything else is a parameter.
      const out: Segment[] = []
      part.quasis.forEach((q, i) => {
        if (i > 0) out.push(...segmentsOf(part.parts[i - 1]!))
        if (q.length > 0) out.push({ text: q })
      })
      return out
    }
    case "returning": {
      const base = part.base
      if (base.kind !== "helper" || (base.name !== "insert" && base.name !== "update")) return dynamic("returning")
      const inner = segmentsOf(base)
      if (part.value.kind === "bind" && typeof part.value.value === "string") return [...inner, { text: ` RETURNING ${part.value.value}` }]
      if (part.value.kind === "template") return [...inner, { text: " RETURNING " }, ...segmentsOf(part.value)]
      // `.returning(sql("id"))` throws in rc.112 (`TypeError: … segments.length`).
      return dynamic("returning")
    }
    case "helper": {
      const { name, args } = part
      switch (name) {
        case "ident": {
          if (args.length !== 1) return dynamic("identifier")
          return [{ text: escapeSqlite(literalText(args[0], "identifier")) }]
        }
        case "literal": {
          if (args.length !== 1) return dynamic("literal")
          const text = literalText(args[0], "literal")
          if (placeholders(text) > 0) return dynamic("placeholder in literal")
          return [{ text }]
        }
        case "unsafe": {
          if (args.length < 1 || args.length > 2) return dynamic("unsafe")
          const text = literalText(args[0], "unsafe text")
          const binds = args.length === 2 ? bindsOf(requireList(args[1], "bind"), "bind") : []
          if (placeholders(text) !== binds.length) return dynamic("placeholder count")
          return [{ text }, ...binds.map((bind) => ({ bind }))]
        }
        case "in": {
          if (args.length === 1) {
            const binds = bindsOf(requireList(args[0], "helper value"), "helper value")
            // rc.112 compiles the empty one-argument form to `IN ()`, a syntax error at run time.
            if (binds.length === 0) return dynamic("empty in")
            return [{ text: `(${binds.map(() => "?").join(",")})` }, ...binds.map((bind) => ({ bind }))]
          }
          if (args.length === 2) {
            const column = literalText(args[0], "identifier")
            const binds = bindsOf(requireList(args[1], "helper value"), "helper value")
            if (binds.length === 0) return [{ text: "1=0" }]
            return [{ text: `${escapeSqlite(column)} IN (${binds.map(() => "?").join(",")})` }, ...binds.map((bind) => ({ bind }))]
          }
          return dynamic("in")
        }
        case "insert": {
          if (args.length !== 1) return dynamic("insert")
          const rows = args[0]?.kind === "list" ? args[0].items.map((r) => requireRecord(r)) : [requireRecord(args[0])]
          if (rows.length === 0) return dynamic("insert")
          const keys = keyOrder(rows[0]!)
          const out: Segment[] = [{ text: `(${keys.map(escapeSqlite).join(",")}) VALUES ${rows.map(() => `(${keys.map(() => "?").join(",")})`).join(",")}` }]
          for (const row of rows) {
            const own = keyOrder(row)
            if (own.length !== keys.length || own.some((k, i) => k !== keys[i])) return dynamic("heterogeneous rows")
            for (const key of keys) out.push({ bind: cell(row.find(([k]) => k === key)![1]) })
          }
          return out
        }
        case "update": {
          if (args.length < 1 || args.length > 2) return dynamic("update")
          const fields = requireRecord(args[0])
          const omit = args.length === 2 ? requireList(args[1], "omit").map((o) => literalText(o, "omit")) : []
          const keys = keyOrder(fields).filter((k) => !omit.includes(k))
          const out: Segment[] = []
          keys.forEach((key, i) => {
            if (i > 0) out.push({ text: ", " })
            out.push({ text: `${escapeSqlite(key)} = ?` }, { bind: cell(fields.find(([k]) => k === key)![1]) })
          })
          return out
        }
        case "and": if (args.length !== 1) return dynamic("and"); return joinFold(requireList(args[0], "clause member"), " AND ", true, "1=1")
        case "or": if (args.length !== 1) return dynamic("or"); return joinFold(requireList(args[0], "clause member"), " OR ", true, "1=1")
        case "csv": {
          if (args.length === 1) {
            const items = requireList(args[0], "clause member")
            return items.length === 0 ? [] : joinFold(items, ",", false, "")
          }
          if (args.length === 2) {
            const prefix = literalText(args[0], "csv prefix")
            const items = requireList(args[1], "clause member")
            return items.length === 0 ? [] : [{ text: `${prefix} ` }, ...joinFold(items, ",", false, "")]
          }
          return dynamic("csv")
        }
        default:
          return unknown(name)
      }
    }
  }
}

/** The fold: the statement's text and its bind parameters as JSON texts, in order, or the
 * refusal. `template` is the tagged template itself. */
export const foldSql = (template: SqlPart & { kind: "template" }): Folded | SqlRefusal => {
  try {
    const segments = segmentsOf(template)
    return {
      text: segments.map((s) => "text" in s ? s.text : "").join(""),
      params: segments.flatMap((s) => "bind" in s ? [s.bind] : []),
    }
  } catch (e) {
    if (e instanceof Refused) return e.refusal
    throw e
  }
}

export const isRefusal = (r: Folded | SqlRefusal): r is SqlRefusal => "code" in r
