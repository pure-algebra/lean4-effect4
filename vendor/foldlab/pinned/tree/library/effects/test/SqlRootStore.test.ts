/**
 * The roots seam over SQL, on a real database file — the second
 * adapter of `RootStore`, which is what makes the seam a seam.
 *
 * Three claims, the same three the file backend's roots registry
 * answers: publication is listed, re-publication is the identity, and
 * a completely fresh composition over the same file lists what the
 * first one published. The third is the durability claim
 * `KvsSqlite.test.ts` proves for bytes, extended to names: Litestream
 * replicates one database file, so the object table and the roots
 * table travel together or not at all.
 *
 * The driver is named here, as it is there, because a test is a
 * composition — the library speaks `SqlClient` and never a database.
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
): Cas.NodeInput => Cas.NodeInput.make({
  kind: { version: 0, tag },
  payload: Uint8Array.from(payload),
  refs: [],
})

/** The whole store over one database: the byte plane over the SQL
 * key-value store, the roots registry over the same client. Both
 * tables live in the one file `KvsSqlite.test.ts` composes. */
const layerSqliteStore = (filename: string) =>
  Layer.mergeAll(Cas.layerStore, Cas.layerSqlRootStore()).pipe(
    Layer.provideMerge(Cas.layerKvsBackend),
    Layer.provide(Layer.mergeAll(
      KeyValueStore.layerSql({ table: "cas_objects" }),
      Cas.layerAddressSha256Live,
    )),
    // `provideMerge` on the client keeps `SqlClient` in the answer, so
    // a test can write a row the seam never would.
    Layer.provideMerge(SqliteClient.layer({ filename })),
  )

it.effect("publish is listed, and publishing the same root again is the identity", () =>
  withStoreRoot((directory) =>
    Effect.gen(function* () {
      const store = yield* Cas.Store
      const roots = yield* Cas.RootStore

      expect(yield* roots.list).toEqual([])

      const first = yield* store.put(node([1, 2, 3], 91))
      const second = yield* store.put(node([4], 92))
      yield* roots.publish(first)
      yield* roots.publish(second)
      // Grow-only and idempotent: the second publication of a resident
      // root leaves the set exactly as it was.
      yield* roots.publish(first)

      expect((yield* roots.list).toSorted()).toEqual([first, second].toSorted())
    }).pipe(Effect.provide(layerSqliteStore(`${directory}/cas.db`)))))

it.effect("a fresh composition over the same file lists what the first published", () =>
  withStoreRoot((directory) => {
    const filename = `${directory}/cas.db`
    const content = node([7, 7, 7], 91)

    return Effect.gen(function* () {
      const published = yield* Effect.gen(function* () {
        const store = yield* Cas.Store
        const roots = yield* Cas.RootStore
        const id = yield* store.put(content)
        yield* roots.publish(id)
        return id
      }).pipe(Effect.provide(layerSqliteStore(filename)))

      // New client, new connection, new seams — only the file is
      // shared. The name survives with the bytes it names.
      yield* Effect.gen(function* () {
        const roots = yield* Cas.RootStore
        const loader = yield* Cas.Loader
        expect(yield* roots.list).toEqual([published])
        expect((yield* loader.load(published)).payload).toEqual(content.payload)
      }).pipe(Effect.provide(layerSqliteStore(filename)))
    })
  }))

it.effect("a row that is not an address is not a published root", () =>
  withStoreRoot((directory) =>
    Effect.gen(function* () {
      const roots = yield* Cas.RootStore
      const admitted = yield* (yield* Cas.Store).put(node([9], 91))
      yield* roots.publish(admitted)

      // A hand-edited or hostile table cannot inject a malformed
      // identifier into a listing: the registry filters, the way the
      // file backend filters a stray file out of roots/.
      const sql = yield* SqlClient.SqlClient
      yield* sql`INSERT INTO ${sql(Cas.defaultRootsTable)} (address) VALUES ('not-an-address')`

      expect(yield* roots.list).toEqual([admitted])
    }).pipe(Effect.provide(layerSqliteStore(`${directory}/cas.db`)))))
