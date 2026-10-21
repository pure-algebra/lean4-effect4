/** sql.ts — the adapter of the SQLite package's rows (`src/Effect4/Program/Packages/SqliteBun.lean`),
 * on rc.112: `Sql` and `SqlHandle`, which `sqliteOpen`, `sqlUnsafe` and `sqliteClose` are bound to.
 *
 * The one file of the prelude that imports `@effect/sql-sqlite-bun`. `prelude.ts` does not import
 * it: a printed module reaches it only by importing `Sql` for a SQL row, so a folder whose modules
 * have no SQL row copies no file that needs the package (`Compiler.Prelude.closure`). The tape and
 * the error projection are the prelude's (`recorded`, `toPair`). */
import { Effect, Exit, Scope } from "effect"
import * as Reactivity from "effect/unstable/reactivity/Reactivity"
import { SqliteClient } from "@effect/sql-sqlite-bun"
import { recorded, toPair } from "./prelude.ts"

/** A row set crossing as `list (list (prod string string))`: one `(column, cell)` pair per
 * column in the driver's order, every cell JSON text (DB-15). */
const rowsToWire = (rows: ReadonlyArray<unknown>): ReadonlyArray<ReadonlyArray<readonly [string, string]>> =>
  rows.map((row) => Object.entries(row as Record<string, unknown>).map(([column, cell]) => [column, JSON.stringify(cell === undefined ? null : cell)] as const))

/** The SQL client handle: the package's client and the scope the prelude minted for it. The
 * one method the table spells, `unsafe`, is the package's own (`sql.unsafe(text, params)`,
 * a `Statement`, the effect that runs it) with each JSON-text parameter decoded before it
 * binds (DB-15: `"7"` binds a number, `"\"x\""` a string) and the rows crossed as pairs. */
export class SqlHandle {
  readonly ["~effect4/ExternalHandle"] = "SqlClient.SqlClient"
  constructor(readonly scope: Scope.Closeable, readonly client: SqliteClient.SqliteClient) {}
  unsafe(text: string, params: ReadonlyArray<string>) {
    return Effect.mapError(recorded("unsafe", [this, text, params],
      Effect.map(this.client.unsafe(text, params.map((p) => JSON.parse(p) as unknown)), rowsToWire)), toPair)
  }
}
export const Sql = {
  /** `SqliteClient.make({ filename, disableWAL: true })` under a scope the prelude mints, so the
   * package's own release (a finalizer it registers on that scope) runs at `Sql.close`.
   * Not projected: the row is typed `error := .never` because `make` is typed `never`, and a
   * file that cannot be opened is a defect `new Database` throws, which no tape replays. */
  open: (filename: string) => recorded("Sql.open", [filename], Effect.gen(function* () {
    const scope = yield* Scope.make()
    const client = yield* SqliteClient.make({ filename, disableWAL: true }).pipe(
      Effect.provideService(Scope.Scope, scope),
      Effect.provide(Reactivity.layer),
    )
    return new SqlHandle(scope, client)
  })),
  close: (handle: SqlHandle) => recorded("Sql.close", [handle], Scope.close(handle.scope, Exit.void)),
}
