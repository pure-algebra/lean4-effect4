/**
 * The published-roots registry over SQL: the naming seam beside the
 * key-value byte plane, written against Effect's abstract `SqlClient`.
 * Nothing here names a database — the composition provides the client,
 * exactly as the file backend is handed a `FileSystem`.
 *
 * Why this module exists at all, stated as honestly as its sibling
 * states its own absence: `KvsBackend` provides read and write and
 * NEVER roots, because `KeyValueStore` carries no key enumeration, so
 * `RootStore.list` cannot be written over it. SQL adds exactly the one
 * capability that was missing — enumeration. `SELECT` over a table of
 * addresses is the listing a key-value store cannot express, and it is
 * the whole reason the roots seam can be served here and not there.
 * Nothing else changes: the byte plane is still the key-value
 * backend's, and this adapter never touches bytes.
 *
 * On-database contract, the table analogue of the file backend's
 * `roots/<64 hex>` directory:
 *
 *     cas_roots(address TEXT PRIMARY KEY)   one row per published root
 *
 * The address is the key, so the row's presence IS the publication and
 * there is nothing else in the row to disagree with it.
 *
 * `publish` is `INSERT ... ON CONFLICT DO NOTHING`: the seam's algebra
 * says the roots set only grows and re-publication is the identity, and
 * an ignored conflict is that algebra in one round trip. The clause is
 * the SQLite and PostgreSQL spelling; MySQL and SQL Server want their
 * own (`INSERT IGNORE`, a `MERGE`) and this adapter does not pretend to
 * serve them — the composition it exists for is the SQLite/Litestream
 * one, and a dialect that refuses the clause fails loudly at its first
 * publish rather than quietly dropping a root.
 *
 * Fail-closed publication is NOT enforced here. The Lean side's
 * `publish_mem` states that a published root must already be resident,
 * and the CLI's `publish` verb is where that gate lives: it loads the
 * address through the full read law before calling this seam. The
 * adapter stays as dumb as its file sibling — it grows a set of
 * strings and judges nothing — because a backend that judged admission
 * would be a second place the store's invariants could weaken.
 *
 * Rows that are not addresses are filtered out of `list` rather than
 * decoded, the same defence `FileBackend.list` keeps against a stray
 * file in `roots/`: a hostile or hand-edited table cannot inject a
 * malformed identifier into a caller's listing.
 */
import { Effect, Layer } from "effect"
import * as SqlClient from "effect/unstable/sql/SqlClient"
import type { SqlError } from "effect/unstable/sql/SqlError"
import {
  BackendFailure,
  RootStore,
  type RootStoreShape,
} from "./Backend.ts"
import { ContentId } from "./Node.ts"

/** The table the registry lives in when the composition does not name
 * one — the roots counterpart of the key-value store's object table. */
export const defaultRootsTable = "cas_roots"

/** Which table the registry lives in. */
export interface SqlRootStoreOptions {
  readonly table?: string
}

const rootHex = /^[0-9a-f]{64}$/u

const failure = (error: SqlError): BackendFailure =>
  new BackendFailure({
    reason: `roots registry failed: ${error.message}`,
    cause: error,
  })

/**
 * Build the roots seam over the `SqlClient` in context, creating the
 * table if it is not there.
 *
 * The `CREATE TABLE` is a composition step, not an operation: a
 * database that refuses it is a defect here, exactly as it is in
 * `KeyValueStore.layerSql` for the object table beside it. One
 * composition, one failure register — the seam's own `BackendFailure`
 * stays reserved for what `publish` and `list` answer.
 */
export const makeSqlRootStore = (
  options: SqlRootStoreOptions = {},
): Effect.Effect<RootStoreShape, never, SqlClient.SqlClient> =>
  Effect.gen(function* () {
    // Without transforms: the column is `address` in the statement and
    // `address` in the row, whatever naming convention the client was
    // configured with.
    const client = (yield* SqlClient.SqlClient).withoutTransforms()
    const table = client(options.table ?? defaultRootsTable)

    yield* client`
      CREATE TABLE IF NOT EXISTS ${table} (
        address TEXT PRIMARY KEY
      )
    `.pipe(Effect.orDie)

    const publish: RootStoreShape["publish"] = Effect.fn(
      "SqlRootStore.publish",
    )(function* (root) {
      return yield* client`
        INSERT INTO ${table} (address) VALUES (${root})
        ON CONFLICT (address) DO NOTHING
      `.pipe(Effect.asVoid, Effect.mapError(failure))
    })

    const list: RootStoreShape["list"] = client<{ readonly address: string }>`
      SELECT address FROM ${table}
    `.pipe(
      Effect.map((rows) => rows
        .map((row) => row.address)
        .filter((address) => rootHex.test(address))
        .map((address) => ContentId.make(address))),
      Effect.mapError(failure),
    )

    return { publish, list }
  })

/** Provide the roots seam from the `SqlClient` in context. The client's
 * realization — SQLite on a file, or any other dialect the clause above
 * serves — is the composition's choice and stays a visible layer
 * requirement. */
export const layerSqlRootStore = (
  options: SqlRootStoreOptions = {},
): Layer.Layer<RootStore, never, SqlClient.SqlClient> =>
  Layer.effect(RootStore, makeSqlRootStore(options))
