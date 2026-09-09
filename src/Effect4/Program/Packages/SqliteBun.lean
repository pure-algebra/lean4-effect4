import Effect4.Program.Native

/-!
# Packages.SqliteBun — the first canonical package table (host rows slice, step 5)

The rows a program may perform against the pinned `@effect/sql-sqlite-bun@4.0.0-rc.112`
client, as a `RowTable` value: external rows (`Registration.external`), answered by the host
through the tape and never modelled by a store. Every row is data the printer, the reader,
the typing and the compile read; nothing here is a hand implementation of the package.

What is the package's, verbatim, and what is modelled (the scouts of 2026-09-09, notes
`docs/research/2026-09-09-host-rows-scout-{tables,sql-ingest,recorder}.md`):

* `unsafe` is the package's own executable pair: `sql.unsafe(text, params)` answers a
  `Statement`, and a `Statement` *is* the effect that runs `connection.execute(sql, params)`
  (`vendor/effect-4.0.0-rc.112/src/unstable/sql/Statement.ts:71`, `:442-445`, `:1383-1391`).
  `SqlClient` has no `execute` and no `query`; the slice's `execute` row is this row. A row
  set crosses as `list (list (prod string string))`, one `(column, cell)` pair per column with
  every cell JSON text; the parameters cross as `list string` of JSON text (DB-15) and the
  printed program builds them with the `strings` atom. The host decodes each parameter with
  `JSON.parse` before binding, so `7` binds a number and `"\"x\""` a string (DB-15, amended
  2026-09-09).
* `open` and `close` are the harness's plumbing around the package, labelled as such: the
  client's constructor `SqliteClient.make(config)` takes a record with `filename` the only
  required field and needs `disableWAL: true` for `:memory:`, and its release is a finalizer
  the constructor registers on its scope — there is no `close` method. The two rows spell a
  prelude pair over a scope the prelude mints, so the machine sees an `acquireRelease` whose
  release is observable. Their `cite` names the package facts they wrap, not a method.
* Errors cross as `prod string string` in rc.112's own two-level form (ruling G1, 2026-09-09):
  the reason's tag (`reason._tag`, the eleven discriminants `Effect.catchReason` dispatches on)
  and the driver's message under it (`reason.cause.message`); the outer `_tag`, the constant
  `"SqlError"`, is implied by the row. Not the literal `(_tag, message)`: this driver builds
  every reason with the constant message `"Failed to execute statement"` and keeps its own
  text under `reason.cause`, so that pair was the same for every statement failure (observed
  2026-09-09). Only `unsafe` has the channel: `make` is typed `never` (an unopenable file is a
  thrown defect) and the release cannot fail.

A program that uses these rows types, prints and reads back only under this table
(`Api.typeOf p sqliteBun`, `Api.print p sqliteBun`, `Api.read e sqliteBun`); its external
indices are the rows' positions here, so the order below is part of the table's identity.
-/

namespace Effect4.Program.Packages

/-- The rc.112 key string of the SQL client service (`unstable/sql/SqlClient.ts:95`), the
`sourceId` a foreign key declaration carries; the printed key spells the service code. -/
def sqlKey : String := "effect/sql/SqlClient"

/-- The error column: the `_tag` and the message (DB-15). -/
def sqlError : Ty := .prod .string .string

/-- A statement's rows: one `(column, cell)` pair per column, every cell JSON text. -/
def sqlRows : Ty := .list (.list (.prod .string .string))

def sqliteBun : RowTable :=
  [ { name := "sqliteOpen", spelling := "Sql.open", shape := .call, kind := .async,
      registration := .external, request := .string, answer := NativeOp.sqlTy, error := .never,
      -- the prelude's constructor call over a minted scope; the package's `make` takes
      -- `{ filename, disableWAL: true }` and registers its own release on that scope. Its
      -- error channel is `never`: `make` is typed `Effect<SqliteClient, never, Scope |
      -- Reactivity>` in `@effect/sql-sqlite-bun`'s `SqliteClient.ts`, and a file that cannot
      -- be opened is a defect thrown by `new Database`, not a `SqlError` (observed 2026-09-09,
      -- the error-paths receipt), so no typed failure can ever answer this row
      cite := "vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlClient.ts:95" }
  , { name := "sqlUnsafe", spelling := "unsafe", shape := .method, kind := .async,
      registration := .external,
      request := .prod NativeOp.sqlTy (.prod .string (.list .string)), answer := sqlRows,
      error := sqlError,
      cite := "vendor/effect-4.0.0-rc.112/src/unstable/sql/Statement.ts:442-445" }
  , { name := "sqliteClose", spelling := "Sql.close", shape := .call, kind := .async,
      registration := .external, request := NativeOp.sqlTy, answer := .unit, error := .never,
      -- closes the minted scope, which runs the package's own finalizer
      cite := "vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlClient.ts:39-84" } ]

end Effect4.Program.Packages
