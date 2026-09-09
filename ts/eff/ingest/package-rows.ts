// The canonical package table for the two foreign readers (host rows step 5): one table, both
// packages in package order (`Effect4.Program.Packages.table`), so an external index either
// engine emits is a position in the same list Lean reads under. The package keys the readers
// admit are exactly the rows of `packages.gen.ts` (ingest spec §5.9, "package keys"): a head
// that resolves through an `effect` import to `<module>.<target>` (a named import of the
// service's barrel) or `<module>/<target>` (a namespace import of its file) is the package's
// key, with the rc.112 key string as its `sourceId` and the service type code as its shape.
import type { Row, Term, Ty } from "../eff.gen.ts"
import { packages, type Package } from "../packages.gen.ts"

/** The canonical table, package rows in package order; the index is `NativeOp.external i`. */
export const packageTable: ReadonlyArray<Row> = packages.flatMap((p) => p.rows)

/** The resolved heads that name a package's key. */
export const packageByHead: ReadonlyMap<string, Package> = new Map(
  packages.flatMap((p) => [[`${p.module}.${p.target}`, p] as const, [`${p.module}/${p.target}`, p] as const]),
)

/** The package whose handle target a `Context.Service<…>` shape names, if any. */
export const packageByTarget = (shape: string): Package | undefined => packages.find((p) => p.target === shape)

/** A method row by its spelling: the receiver is the first component of its request
 * (`RowShape.method`); trailing names are never printed on a method row. */
export const methodRow = (spelling: string): { readonly index: number; readonly row: Row } | undefined => {
  const index = packageTable.findIndex((r) => r.spelling === spelling && r.shape === "method" && r.trailing.length === 0)
  return index < 0 ? undefined : { index, row: packageTable[index]! }
}

/** The argument view of a method row (`Print.lean` `methodArgsRow`): the second component of
 * the declared `prod`, read as a tuple call when it is itself a `prod`, a unit call when it is
 * `unit`, one argument otherwise. */
export const methodArgs = (row: Row): { readonly count: 0 | 1 | 2; readonly types: ReadonlyArray<Ty> } => {
  const args: Ty = row.request._tag === "prod" ? row.request.right : { _tag: "never" }
  if (args._tag === "prod") return { count: 2, types: [args.left, args.right] }
  if (args._tag === "unit") return { count: 0, types: [] }
  return { count: 1, types: [args] }
}

/** Whether a row position is a `list string`: a bind-parameter list, which foreign code writes
 * as an array literal and DB-15 carries as JSON text through the `strings` atom. */
export const isStringList = (ty: Ty): boolean => ty._tag === "list" && ty.inner._tag === "string"

/** The JSON text of an admitted bind literal (DB-15: `7` is `"7"`, `"a"` is `"\"a\""`, `null`
 * is `"null"`); `undefined` for anything outside the alphabet. */
export const bindText = (value: number | string | boolean | null): string | undefined => {
  if (value === null) return "null"
  if (typeof value === "boolean") return value ? "true" : "false"
  if (typeof value === "number") return Number.isSafeInteger(value) && value >= 0 ? String(value) : undefined
  return JSON.stringify(value)
}

/** `strings(t₁, …, tₙ)` over JSON texts. */
export const stringsTerm = (texts: ReadonlyArray<string>): Term =>
  ({ _tag: "app", atom: "strings", args: texts.map((value) => ({ _tag: "lit", value: { _tag: "str", value } })) })
