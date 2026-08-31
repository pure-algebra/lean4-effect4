/**
 * The SQLite path: the whole store law over the key-value backend over
 * `KeyValueStore.layerSql`, on a real database file. This is the
 * Litestream composition — Litestream replicates the file underneath,
 * and the client opens it in WAL mode by default, which is what
 * Litestream requires.
 *
 * The claim proved here is durability across compositions: content
 * admitted by one composition is served by a completely fresh one over
 * the same file, address recomputed and canonical decode re-run. The
 * driver is a dev dependency on purpose — the library speaks
 * `KeyValueStore` and never names a database, exactly as it speaks
 * `FileSystem` and never names a disk.
 */
import { SqliteClient } from "@effect/sql-sqlite-bun"
import { expect, it } from "@effect/vitest"
import { Effect, Layer } from "effect"
import * as KeyValueStore from "effect/unstable/persistence/KeyValueStore"
import * as SqlClient from "effect/unstable/sql/SqlClient"
import { Cas } from "../src/index.ts"
import { withStoreRoot } from "./fixtures/diskFs.ts"

const node = (
  payload: ReadonlyArray<number>,
  tag: number,
  refs: Cas.NodeInput["refs"] = [],
): Cas.NodeInput => Cas.NodeInput.make({
  kind: { version: 0, tag },
  payload: Uint8Array.from(payload),
  refs,
})

/** THE production composition: the store law over the byte plane over
 * a SQL key-value store over one SQLite file. Swap the client layer
 * and the same stack runs on Postgres or MySQL; nothing above the
 * key-value seam changes. */
const layerSqliteCas = (filename: string) =>
  Cas.layerStore.pipe(
    Layer.provideMerge(Cas.layerKvsBackend),
    Layer.provide(Layer.mergeAll(
      KeyValueStore.layerSql({ table: "cas_objects" }),
      Cas.layerAddressSha256Live,
    )),
    Layer.provide(SqliteClient.layer({ filename })),
  )

it.effect("a fresh composition over the same file serves what the first admitted", () =>
  withStoreRoot((directory) => {
    const filename = `${directory}/cas.db`
    const child = node([1, 2, 3], 91)

    return Effect.gen(function* () {
      const admitted = yield* Effect.gen(function* () {
        const store = yield* Cas.Store
        const childId = yield* store.put(child)
        const parentId = yield* store.put(
          node([4], 92, [{ expectedTag: 91, id: childId }]),
        )
        return { childId, parentId }
      }).pipe(Effect.provide(layerSqliteCas(filename)))

      // A completely fresh composition: new client, new connection, new
      // store law — only the file is shared.
      yield* Effect.gen(function* () {
        const store = yield* Cas.Store
        const reader = yield* Cas.ByteReader

        const loaded = yield* store.load(admitted.childId)
        expect(loaded.payload).toEqual(child.payload)
        expect(loaded.kind.tag).toBe(91)

        const absent = Cas.ContentId.make("cd".repeat(32))
        expect(yield* reader.presence([
          admitted.childId,
          admitted.parentId,
          absent,
        ])).toEqual(["present", "present", "missing"])

        // Re-admitting identical content is the identity, across
        // compositions as within one.
        const store2 = yield* Cas.Store
        expect(yield* store2.put(child)).toBe(admitted.childId)
      }).pipe(Effect.provide(layerSqliteCas(filename)))
    })
  }))

it.effect("the client opens the database in WAL mode — what Litestream requires", () =>
  withStoreRoot((directory) =>
    Effect.gen(function* () {
      const sql = yield* SqlClient.SqlClient
      const rows = yield* sql<{ journal_mode: string }>`PRAGMA journal_mode`
      expect(rows[0]?.journal_mode).toBe("wal")
    }).pipe(Effect.provide(
      SqliteClient.layer({ filename: `${directory}/cas.db` }),
    ))))
