/**
 * BG-2 — the bound in the STATEMENT, read off the statement itself.
 *
 * Contract packet: `.staging/frontend-trunk/packets/S1-HISTORY-ROUTE.md`,
 * L-A13 BG-2 ("SEAM OWED BY THE IMPLEMENTER"). This file is that
 * obligation discharged; it is the implementer's, not the breaker's,
 * and it sits beside `WordLogPaging.test.ts` rather than inside it.
 *
 * ## Why a black-box case cannot close this
 *
 * `WordLogPaging.test.ts`'s S-7 (BG-1a) kills
 * read-all-then-DECODE: a sqlite row beyond the page that does not
 * decode as a receipt does not refuse the page, which witnesses that
 * the rows past the page were never handed to the schema. It does NOT
 * kill read-all-then-SLICE-then-decode — an implementation that
 * SELECTs the whole suffix, cuts the page in JS, and decodes only the
 * cut passes S-7 exactly, while still transferring every row out of
 * the database. That is QE-A2's memory hazard at the driver rather
 * than at the decoder, and no observation through `WordLogShape` can
 * tell the two apart: the seam answers the same document either way.
 *
 * So the observation is taken one level down, at the seam's own
 * dependency. `makeSqlWordLog` builds over whatever `SqlClient` is in
 * context; this file provides a RECORDING one — the real Bun SQLite
 * client behind a proxy that keeps the compiled text of every
 * statement the seam constructs — and asserts the bound is in the SQL.
 *
 * No `src` API changes for this. The seam is already parameterized by
 * its client; the test tree supplies a different one, which is what a
 * seam being a seam means.
 */
import { SqliteClient } from "@effect/sql-sqlite-bun"
import { expect, it } from "@effect/vitest"
import { Effect } from "effect"
import * as SqlClient from "effect/unstable/sql/SqlClient"
import type * as Statement from "effect/unstable/sql/Statement"
import { Cas } from "../src/index.ts"
import { withStoreRoot } from "./fixtures/diskFs.ts"

/** A statement, once it has been compiled to text. `Statement<A>` is
 * the only thing the client constructs that carries `compile`; an
 * identifier fragment (`client("cas_word")`) does not, and is skipped. */
const compiledText = (value: unknown): string | undefined => {
  const candidate = value as { readonly compile?: unknown } | null
  if (candidate === null || typeof candidate !== "object") return undefined
  if (typeof candidate.compile !== "function") return undefined
  return (candidate as Statement.Statement<never>).compile()[0]
}

/**
 * The real client, wearing a tap.
 *
 * Every call of the client — the tagged-template form is the only one
 * this seam uses — is forwarded untouched, and the statement it
 * returns is compiled once and its SQL kept. The proxy reproduces
 * itself through `withoutTransforms()`, which `makeSqlWordLog` calls
 * before it builds anything, so the recording survives the seam's own
 * first move.
 *
 * The record is of statements CONSTRUCTED. For this seam that is the
 * same set as statements issued: `SqlWordLog.since` builds exactly the
 * statements it then yields, and builds no others.
 */
const recordingClient = (
  client: SqlClient.SqlClient,
  recorded: Array<string>,
): SqlClient.SqlClient =>
  new Proxy(client, {
    apply(target, thisArg, args) {
      const result = Reflect.apply(
        target as unknown as (...values: ReadonlyArray<unknown>) => unknown,
        thisArg,
        args,
      )
      const text = compiledText(result)
      if (text !== undefined) recorded.push(text)
      return result
    },
    get(target, property, receiver) {
      if (property === "withoutTransforms") {
        return () => recordingClient(target.withoutTransforms(), recorded)
      }
      const value = Reflect.get(target, property, receiver) as unknown
      return typeof value === "function" ? value.bind(target) : value
    },
  }) as SqlClient.SqlClient

/** The statements a read issued, with the ones every read issues —
 * table creation, the cursor aggregate — left in: the assertions below
 * are about the RECEIPT SELECT, and naming it by its columns rather
 * than by its position in the list keeps them honest if the seam ever
 * issues another. */
const receiptSelects = (recorded: ReadonlyArray<string>): ReadonlyArray<string> =>
  recorded.filter((sql) =>
    sql.includes("SELECT") && sql.includes("address") && sql.includes("WHERE")
  )

const withRecordedRead = <A>(
  use: (
    log: Cas.WordLogShape,
    recorded: Array<string>,
  ) => Effect.Effect<A, Cas.BackendFailure>,
): Effect.Effect<A, unknown> =>
  withStoreRoot((root) =>
    Effect.gen(function* () {
      const real = yield* SqlClient.SqlClient
      const recorded: Array<string> = []
      const log = yield* Cas.makeSqlWordLog().pipe(
        Effect.provideService(SqlClient.SqlClient, recordingClient(real, recorded)),
      )
      for (let index = 0; index < 6; index += 1) {
        yield* log.append({
          address: String(index).padStart(64, "0"),
          at: 1_700_000_000_000 + index,
          size: index + 1,
          tag: 0,
        })
      }
      // Only the READ is under test, so the appends' statements are
      // dropped before it runs.
      recorded.length = 0
      return yield* use(log, recorded)
    }).pipe(Effect.provide(SqliteClient.layer({ filename: `${root}/cas.db` }))))

it.effect("BG-2 the receipt SELECT carries a LIMIT — the page bound is in the statement, not in a slice after it", () =>
  withRecordedRead((log, recorded) =>
    Effect.gen(function* () {
      const page = yield* log.since(0, 2)
      expect(page.word.map((entry) => entry.seq)).toEqual([0, 1])

      const selects = receiptSelects(recorded)
      expect(selects, "the read issued no receipt SELECT to inspect").toHaveLength(1)
      // THE ASSERTION the packet owes. An implementation that SELECTs
      // the suffix and cuts it in JS passes every black-box case in the
      // battery — S-7 included — and fails here, which is the only
      // place the difference is observable.
      expect(
        selects[0],
        "BG-2: the statement transfers every row past the page — the bound must be in the SQL",
      ).toContain("LIMIT")
    })))

it.effect("BG-2 the default read is bounded too — an absent `limit` is the cap, not the absence of one", () =>
  withRecordedRead((log, recorded) =>
    Effect.gen(function* () {
      // The unbounded pull is the one QE-A2 actually names: `since(0)`
      // with no bound at all, on a word large enough to matter. The
      // seam's default is what closes it, so the default read must
      // carry the clause as well.
      yield* log.since(0)
      const selects = receiptSelects(recorded)
      expect(selects).toHaveLength(1)
      expect(selects[0]).toContain("LIMIT")
    })))

it.effect("BG-2 a read past the end adds one aggregate and still no unbounded scan", () =>
  withRecordedRead((log, recorded) =>
    Effect.gen(function* () {
      // The empty-page branch asks the word for its end. That is one
      // aggregate row by construction — the page above never widens to
      // find it — and this case pins that the branch does not reach
      // for the rows instead.
      const page = yield* log.since(99, 3)
      expect(page).toEqual({ next: 6, word: [] })

      const selects = receiptSelects(recorded)
      expect(selects).toHaveLength(1)
      expect(selects[0]).toContain("LIMIT")
      const aggregates = recorded.filter((sql) => sql.includes("MAX(seq)"))
      expect(aggregates).toHaveLength(1)
      expect(aggregates[0]).not.toContain("address")
    })))
