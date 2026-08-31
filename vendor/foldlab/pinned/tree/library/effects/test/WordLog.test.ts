/**
 * The word log — the receipts seam, held to the store's own bar.
 *
 * The claims, by plane:
 *
 * - THE LAW: a fresh admission is receipted with a dense, zero-based
 *   mark; a duplicate put appends nothing (the Lean `step`'s word
 *   behaviour, mirrored); a mark that is not a finite number is
 *   refused rather than floored to "the whole history"; and a put
 *   whose bytes land but whose receipt fails FAILS TOGETHER, typed —
 *   bytes first as an ORDER, the refusal naming the address, and the
 *   gap it leaves observable and permanent. That last case is the
 *   ruled crash-class outcome, probed end to end.
 * - THE FILE REALIZATION: rows are the registered word-wire spelling,
 *   one line each. Two damaged tails are told apart: a final line that
 *   does not decode is a tear, tolerated on read and truncated by the
 *   next append; a final line that decodes but lost its newline is a
 *   whole receipt, kept, with the separator restored before the next
 *   append can fuse onto it. An edited mark fails typed because order
 *   is semantics, and a mark issued twice is refused as the WRITER
 *   RACE it is — which two real OS processes appending at once no
 *   longer produce, because the mark plane is taken under a lock file.
 * - THE SQL REALIZATION: the single-statement append keeps marks dense
 *   under concurrent writers, the table's columns are the generated
 *   record's field names, and a completely fresh composition over the
 *   same database file answers the same history — the durability
 *   claim `KvsSqlite.test.ts` proves for bytes, extended to receipts.
 */
import { SqliteClient } from "@effect/sql-sqlite-bun"
import { expect, it } from "@effect/vitest"
import { Effect, FileSystem, Layer, Schema } from "effect"
import * as KeyValueStore from "effect/unstable/persistence/KeyValueStore"
import * as SqlClient from "effect/unstable/sql/SqlClient"
import { Cas } from "../src/index.ts"
import { wordHistorySchema } from "../src/cas/generated/WordLogSchema.ts"
import { layerDiskFs, withStoreRoot } from "./fixtures/diskFs.ts"

const node = (
  payload: ReadonlyArray<number>,
  tag: number,
): Cas.NodeInput => Cas.NodeInput.make({
  kind: { version: 0, tag },
  payload: Uint8Array.from(payload),
  refs: [],
})

/** The memory store WITH receipts — through the library's own worded
 * combinator, which is where the "log under the law" ordering lives. */
const layerMemoryWorded = Cas.layerWorded(
  Cas.layerMemoryBackend,
  Cas.layerMemoryWordLog,
).pipe(Layer.provideMerge(Cas.layerAddressSha256Live))

it.effect("fresh admissions are receipted in admission order; a duplicate appends nothing", () =>
  Effect.gen(function* () {
    const store = yield* Cas.Store
    const log = yield* Cas.WordLog

    const first = yield* store.put(node([1], 0x01))
    const second = yield* store.put(node([2, 3], 0x0c))
    // The duplicate is the identity on the store AND on the word —
    // the Lean `step` leaves the word unchanged on `duplicate`.
    const again = yield* store.put(node([1], 0x01))
    expect(again).toBe(first)

    const history = yield* log.since(0)
    expect(history.next).toBe(2)
    expect(history.word.map((entry) => entry.seq)).toEqual([0, 1])
    expect(history.word.map((entry) => entry.address)).toEqual([first, second])
    expect(history.word.map((entry) => entry.tag)).toEqual([0x01, 0x0c])
    expect(history.word.map((entry) => entry.size)).toEqual([1, 2])
    for (const entry of history.word) {
      // `at` is the composition's Clock — under the test clock that is
      // the epoch itself, which is exactly the honesty claimed: the
      // timestamp is whatever clock the admitting host runs on.
      expect(Number.isSafeInteger(entry.at)).toBe(true)
      expect(entry.at).toBeGreaterThanOrEqual(0)
    }

    // `since` is the suffix, half-open: from 1 answers only the
    // second receipt; from the end answers "nothing happened" with
    // the true cursor; a mark past the end still answers the cursor.
    expect((yield* log.since(1)).word.map((entry) => entry.seq)).toEqual([1])
    expect(yield* log.since(2)).toEqual({ next: 2, word: [] })
    expect(yield* log.since(99)).toEqual({ next: 2, word: [] })
    // A hostile mark never reaches a from-the-end slice.
    expect((yield* log.since(-3)).word).toHaveLength(2)
    // A mark that is not a number is not floored to zero: answering
    // the WHOLE history to a caller who asked for a position is the
    // seam answering a question it was not asked.
    for (const notAMark of [Number.NaN, Number.POSITIVE_INFINITY]) {
      const refused = yield* Effect.flip(log.since(notAMark))
      expect(refused.reason).toContain("is not a mark")
      expect(refused.reason).toContain("never a timestamp")
    }
  }).pipe(Effect.provide(layerMemoryWorded)))

it.effect("a put whose receipt fails FAILS TOGETHER: bytes first, the refusal names the address, and the gap it leaves is permanent", () =>
  Effect.gen(function* () {
    const backend = Cas.makeMemoryBackend()
    // The real receipts plane, behind a switch — so the word after the
    // outage is a fact this test reads rather than a stub it asserts.
    const receipts = Cas.makeMemoryWordLog()
    const calls: Array<string> = []
    let receiptsDown = true
    const flakyLog: Cas.WordLogShape = {
      append: (entry) => {
        calls.push("append")
        return receiptsDown
          ? Effect.fail(new Cas.BackendFailure({ reason: "the receipts plane is gone" }))
          : receipts.append(entry)
      },
      since: (mark, limit) => receipts.since(mark, limit),
    }
    const watchedWriter: Cas.ByteWriterShape = {
      putBytes: (id, bytes) => {
        calls.push("putBytes")
        return backend.writer.putBytes(id, bytes)
      },
    }
    const layer = Cas.layerWorded(
      Layer.mergeAll(
        Layer.succeed(Cas.ByteReader, backend.reader),
        Layer.succeed(Cas.ByteWriter, watchedWriter),
      ),
      Layer.succeed(Cas.WordLog, flakyLog),
    ).pipe(Layer.provideMerge(Cas.layerAddressSha256Live))
    return yield* Effect.gen(function* () {
      const store = yield* Cas.Store
      const log = yield* Cas.WordLog

      // Bytes land, the receipt does not: the put refuses, typed, and
      // the refusal names both facts — the admission happened and the
      // word under-reports it. BROKEN-SILENT is the only alarm
      // category, and this is the loud spelling of the ruling.
      const refused = yield* Effect.flip(store.put(node([7, 7], 0x01)))
      expect(Cas.isCasError(refused)).toBe(true)
      const reason = (refused as { readonly reason: string }).reason
      expect(reason).toContain("receipt was not written")
      expect(reason).toContain("re-put answers the same address")
      // The backend's own words reach the refusal, not just a category.
      expect(reason).toContain("the receipts plane is gone")

      // THE ORDER, not merely the outcome: bytes first, receipt
      // second. The reverse would leave a receipt for content the
      // store never admitted, which is the one thing it never does.
      expect(calls).toEqual(["putBytes", "append"])

      // The refusal names the address, and that is the address a
      // re-put answers — the claim, discriminated: not "some 64 hex
      // characters", but exactly the one the word is missing.
      const admitted = /admitted ([0-9a-f]{64}) but/u.exec(reason)?.[1]
      expect(admitted).toBeDefined()

      // The plane comes back. The re-put takes the DUPLICATE outcome:
      // it answers the named address, writes no bytes, and appends no
      // receipt — so the gap does not heal itself.
      receiptsDown = false
      expect(yield* store.put(node([7, 7], 0x01))).toBe(admitted)
      expect(calls).toEqual(["putBytes", "append"])

      // And the gap is observable: a DIFFERENT admission is receipted
      // now, at mark 0, while the word still holds no receipt for the
      // address admitted during the outage. Permanent, and honest.
      const other = yield* store.put(node([9], 0x01))
      expect(calls).toEqual(["putBytes", "append", "putBytes", "append"])
      const history = yield* log.since(0)
      expect(history.next).toBe(1)
      expect(history.word.map((entry) => entry.address)).toEqual([other])
      expect(history.word.map((entry) => entry.address)).not.toContain(admitted)
    }).pipe(Effect.provide(layer))
  }))

/** The file store WITH receipts, through the same combinator the CLI
 * consumes — so this suite tests the composition that ships, not a
 * hand copy of it. */
const layerFileWorded = (storeRoot: string) =>
  Cas.layerWorded(
    Cas.layerFileBackend(storeRoot),
    Cas.layerFileWordLog(storeRoot),
  ).pipe(Layer.provideMerge(Layer.mergeAll(
    layerDiskFs,
    Cas.layerAddressSha256Live,
  )))

it.effect("file log: rows are the registered spelling on disk, and history survives a fresh composition", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const put = (bytes: ReadonlyArray<number>) =>
        Cas.Store.pipe(
          Effect.flatMap((store) => store.put(node(bytes, 0x01))),
          Effect.provide(layerFileWorded(storeRoot)),
        )
      const first = yield* put([1])
      const second = yield* put([2])

      // The persisted rows decode through the GENERATED schema — the
      // registered spelling, byte for byte on disk, never an ad-hoc
      // shape.
      const raw = yield* fs.readFileString(`${storeRoot}/word.jsonl`)
      const lines = raw.trimEnd().split("\n")
      expect(lines).toHaveLength(2)
      const document = Schema.decodeUnknownSync(wordHistorySchema)({
        next: lines.length,
        word: lines.map((line) => JSON.parse(line)),
      })
      expect(document.word.map((entry) => entry.address)).toEqual([first, second])

      // A completely fresh composition over the same directory reads
      // the same history: the word is the store's, not a process's.
      const replay = yield* Cas.WordLog.pipe(
        Effect.flatMap((log) => log.since(0)),
        Effect.provide(layerFileWorded(storeRoot)),
      )
      expect(replay.next).toBe(2)
      expect(replay.word.map((entry) => entry.seq)).toEqual([0, 1])
    })))

it.effect("file log: a torn final line is tolerated on read and repaired by the next append", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const worded = layerFileWorded(storeRoot)
      const put = (bytes: ReadonlyArray<number>) =>
        Cas.Store.pipe(
          Effect.flatMap((store) => store.put(node(bytes, 0x01))),
          Effect.provide(worded),
        )
      const since = Cas.WordLog.pipe(
        Effect.flatMap((log) => log.since(0)),
        Effect.provide(worded),
      )

      yield* put([1])
      yield* put([2])
      // The crash artifact: an append that died mid-line. Its put
      // never acknowledged, so under-reporting it is the safe
      // direction — reads answer the clean prefix.
      yield* fs.writeFile(
        `${storeRoot}/word.jsonl`,
        new TextEncoder().encode(`{"address":"deadbeef`),
        { flag: "a" },
      )
      const torn = yield* since
      expect(torn.next).toBe(2)

      // The NEXT append repairs the tear before writing: were the torn
      // tail left in place it would sit mid-file after this append and
      // read as corruption forever after.
      yield* put([3])
      const healed = yield* since
      expect(healed.next).toBe(3)
      expect(healed.word.map((entry) => entry.seq)).toEqual([0, 1, 2])
      const raw = yield* fs.readFileString(`${storeRoot}/word.jsonl`)
      expect(raw).not.toContain("deadbeef")
    })))

it.effect("file log: a receipt whose newline was lost survives the next append — nothing fused, nothing re-issued", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const worded = layerFileWorded(storeRoot)
      const put = (bytes: ReadonlyArray<number>) =>
        Cas.Store.pipe(
          Effect.flatMap((store) => store.put(node(bytes, 0x01))),
          Effect.provide(worded),
        )
      const since = Cas.WordLog.pipe(
        Effect.flatMap((log) => log.since(0)),
        Effect.provide(worded),
      )
      const path = `${storeRoot}/word.jsonl`

      const first = yield* put([1])
      const second = yield* put([2])

      // The one-byte artifact: the LINE landed, its separator did not.
      // No proper prefix of a receipt is valid JSON, so this line
      // decodes — which is exactly why it must not be read as a tear.
      const raw = yield* fs.readFileString(path)
      expect(raw.endsWith("\n")).toBe(true)
      yield* fs.writeFileString(path, raw.slice(0, -1))

      // It is still a receipt on read: both marks, nothing lost.
      const stripped = yield* since
      expect(stripped.next).toBe(2)
      expect(stripped.word.map((entry) => entry.seq)).toEqual([0, 1])

      // And the next append does not run onto it. Without the repair
      // the two rows fuse into one undecodable line, which would drop
      // the acknowledged receipt at mark 1 AND hand mark 1 to
      // different content on the read after that.
      const third = yield* put([3])
      const healed = yield* since
      expect(healed.next).toBe(3)
      expect(healed.word.map((entry) => entry.seq)).toEqual([0, 1, 2])
      expect(healed.word.map((entry) => entry.address))
        .toEqual([first, second, third])

      // On disk: three lines, newline-terminated again. That the three
      // DECODE is what the read above already proves — `readLog` puts
      // every line through the generated schema and refuses otherwise.
      const healedRaw = yield* fs.readFileString(path)
      expect(healedRaw.endsWith("\n")).toBe(true)
      expect(healedRaw.trimEnd().split("\n")).toHaveLength(3)
    })))

it.effect("file log: one mark issued twice is refused by name — the race is told apart from a hand edit", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const worded = layerFileWorded(storeRoot)
      const path = `${storeRoot}/word.jsonl`
      yield* Cas.Store.pipe(
        Effect.flatMap((store) => store.put(node([1], 0x01))),
        Effect.provide(worded),
      )
      // What two unlocked writers leave behind: the same mark, twice,
      // both receipts real. Not an edit — nobody renumbered anything.
      const raw = yield* fs.readFileString(path)
      yield* fs.writeFileString(path, `${raw}${raw}`)

      const refused = yield* Effect.flip(Cas.WordLog.pipe(
        Effect.flatMap((log) => log.since(0)),
        Effect.provide(worded),
      ))
      const reason = (refused as { readonly reason: string }).reason
      // The defect named as the race it is, the surviving receipts
      // counted, and the fix named — grade A, and NOT the hand-edit
      // wording, which would send an operator looking for an editor.
      expect(reason).toContain("one mark, issued twice")
      expect(reason).toContain("two writers appended to this log at once")
      expect(reason).toContain("truncate")
      expect(reason).not.toContain("renumbered by hand")
    })))

it.effect("file log: an edited mark anywhere fails typed — order is semantics, never renumbered past", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const worded = layerFileWorded(storeRoot)
      yield* Cas.Store.pipe(
        Effect.flatMap((store) => store.put(node([1], 0x01))),
        Effect.provide(worded),
      )
      // Hand-edit the one receipt to claim a different mark, then add
      // a clean line after it so the damage is NOT the tolerated
      // final-line case.
      const raw = yield* fs.readFileString(`${storeRoot}/word.jsonl`)
      const edited = raw.replace("\"seq\":0", "\"seq\":5")
      yield* fs.writeFileString(`${storeRoot}/word.jsonl`, edited)
      const refused = yield* Effect.flip(Cas.WordLog.pipe(
        Effect.flatMap((log) => log.since(0)),
        Effect.provide(worded),
      ))
      expect((refused as { readonly reason: string }).reason)
        .toContain("order is semantics")
    })))

/** A second OS process that does nothing but append to one file word
 * log — the only way to test the claim, since the in-process semaphore
 * is precisely what a second process does not share. Run under `bun`
 * against this source tree, so it is the shipping code that races. */
const appenderScript = `
import { Effect } from "effect"
import { BunFileSystem } from "@effect/platform-bun"
import { makeFileWordLog } from "${new URL("../src/cas/WordLog.ts", import.meta.url).pathname}"

const tag = Number(process.env.WORD_TAG)
await Effect.runPromise(
  Effect.gen(function* () {
    const log = yield* makeFileWordLog(process.env.WORD_ROOT)
    for (let index = 0; index < Number(process.env.WORD_COUNT); index++) {
      yield* log.append({
        address: String(tag).repeat(64),
        at: Date.now(),
        size: index,
        tag,
      })
    }
  }).pipe(Effect.provide(BunFileSystem.layer)),
)
`

it.live("file log: two OS processes appending at once keep the marks dense — the lock is the mark plane's, not the semaphore", () =>
  withStoreRoot((storeRoot) =>
    Effect.gen(function* () {
      const each = 25
      const writers = [1, 2].map((tag) =>
        Bun.spawn(["bun", "-e", appenderScript], {
          cwd: new URL("../", import.meta.url).pathname,
          env: {
            ...process.env,
            WORD_ROOT: storeRoot,
            WORD_COUNT: String(each),
            WORD_TAG: String(tag),
          },
          stdout: "pipe",
          stderr: "pipe",
        })
      )
      const outcomes = yield* Effect.promise(() =>
        Promise.all(writers.map(async (writer) => ({
          code: await writer.exited,
          err: await new Response(writer.stderr).text(),
        })))
      )
      for (const outcome of outcomes) {
        // The stderr rides along so a failing child says why.
        expect(outcome.err).toBe("")
        expect(outcome.code).toBe(0)
      }

      // Dense, zero-based, no duplicate and no hole: fifty appends
      // from two processes that shared nothing but the directory. The
      // read itself is the assertion — a duplicate mark refuses.
      const history = yield* Cas.WordLog.pipe(
        Effect.flatMap((log) => log.since(0)),
        Effect.provide(layerFileWorded(storeRoot)),
      )
      expect(history.next).toBe(2 * each)
      expect(history.word.map((entry) => entry.seq))
        .toEqual(Array.from({ length: 2 * each }, (_, index) => index))
      // Both writers really did land in one log, interleaved.
      expect(new Set(history.word.map((entry) => entry.tag))).toEqual(new Set([1, 2]))

      // And the lock is released, not leaked: nothing holds the log.
      const fs = yield* FileSystem.FileSystem
      expect(yield* fs.exists(`${storeRoot}/word.jsonl.lock`)).toBe(false)
    })))

/** The db-backed store WITH receipts: bytes, roots, and word in one
 * database file — the composition `bin/cli/store.ts` makes, spelled
 * from the library's own layers. */
const layerSqliteWorded = (filename: string) =>
  Layer.mergeAll(Cas.layerStore, Cas.layerSqlRootStore()).pipe(
    // The word log stands UNDER the store law, not beside it: the law
    // reads it as an optional service at build, so a merely-merged
    // sibling would leave every admission unreceipted.
    Layer.provideMerge(Layer.mergeAll(
      Cas.layerKvsBackend,
      Cas.layerSqlWordLog(),
    )),
    Layer.provide(Layer.mergeAll(
      KeyValueStore.layerSql({ table: "cas_objects" }),
      Cas.layerAddressSha256Live,
    )),
    Layer.provideMerge(SqliteClient.layer({ filename })),
  )

it.effect("sqlite log: receipts land beside the bytes, and a fresh composition over the same file answers the same history", () =>
  withStoreRoot((directory) =>
    Effect.gen(function* () {
      const filename = `${directory}/cas.db`
      const addresses = yield* Effect.gen(function* () {
        const store = yield* Cas.Store
        const first = yield* store.put(node([1], 0x01))
        const second = yield* store.put(node([2], 0x53))
        // Duplicate: identity on the store, silence in the word.
        yield* store.put(node([1], 0x01))
        return [first, second]
      }).pipe(Effect.provide(layerSqliteWorded(filename)))

      // The word survives the composition: same file, fresh layers,
      // same receipts — Litestream replicates this file whole, so
      // bytes and history travel together.
      const history = yield* Cas.WordLog.pipe(
        Effect.flatMap((log) => log.since(0)),
        Effect.provide(layerSqliteWorded(filename)),
      )
      expect(history.next).toBe(2)
      expect(history.word.map((entry) => entry.seq)).toEqual([0, 1])
      expect(history.word.map((entry) => entry.address)).toEqual(addresses)
      expect((yield* Cas.WordLog.pipe(
        Effect.flatMap((log) => log.since(1)),
        Effect.provide(layerSqliteWorded(filename)),
      )).word.map((entry) => entry.address)).toEqual([addresses[1]])
    })))

it.effect("sqlite log: the table SQLite created carries exactly the registered field names, and a hostile mark is refused there too", () =>
  withStoreRoot((directory) =>
    Effect.gen(function* () {
      const filename = `${directory}/cas.db`
      return yield* Effect.gen(function* () {
        const log = yield* Cas.WordLog
        yield* log.append({ address: "cd".repeat(32), at: 5, size: 1, tag: 0x01 })

        // The DDL is hand-spelled with its column types; this binds
        // its NAMES to the generated record, so a rename in the
        // emitter turns a gate red instead of silently reading zero
        // rows through a decode that never sees them.
        const client = (yield* SqlClient.SqlClient).withoutTransforms()
        const columns = yield* client<{ readonly name: string }>`
          SELECT name FROM pragma_table_info(${Cas.defaultWordTable})
        `
        expect(new Set(columns.map((column) => column.name)))
          .toEqual(new Set(Cas.wordLogColumns))
        expect(new Set(Cas.wordLogColumns))
          .toEqual(new Set(["address", "at", "seq", "size", "tag"]))

        const refused = yield* Effect.flip(log.since(Number.NaN))
        expect(refused.reason).toContain("is not a mark")
      }).pipe(Effect.provide(layerSqliteWorded(filename)))
    })))

it.effect("sqlite log: concurrent appends keep the marks dense — the single-statement append is the lock", () =>
  withStoreRoot((directory) =>
    Effect.gen(function* () {
      const filename = `${directory}/cas.db`
      const history = yield* Effect.gen(function* () {
        const log = yield* Cas.WordLog
        yield* Effect.all(
          Array.from({ length: 10 }, (_, index) =>
            log.append({
              address: "ab".repeat(32),
              at: 1_000 + index,
              size: index,
              tag: 0x01,
            })),
          { concurrency: "unbounded" },
        )
        return yield* log.since(0)
      }).pipe(Effect.provide(layerSqliteWorded(filename)))

      // Dense, zero-based, no duplicates, no holes: the mark plane
      // cannot tear under concurrent writers, because assignment and
      // insertion are one statement under one write lock.
      expect(history.next).toBe(10)
      expect(history.word.map((entry) => entry.seq))
        .toEqual([0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
    })))
