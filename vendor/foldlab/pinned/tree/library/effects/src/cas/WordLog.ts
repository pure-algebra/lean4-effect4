/**
 * The word log: the store's own history, persisted — the receipts
 * seam beside the byte and naming planes.
 *
 * The store is a SET (address ⇀ bytes, grow-only); the word is
 * strictly more — bindings in admission order — and until this seam
 * existed the running system dropped it: `cas_run`'s reply was the
 * word for that call and nothing persisted it. This seam is where the
 * running system keeps its word. `append` records one admission;
 * `since` answers the RECEIPTS from a mark.
 *
 * Receipts are a PROJECTION of the Lean model's `WordE.since`
 * (`Cas/Lang/Worded.lean`), not that operation realized: the model's
 * answer is a suffix of the word, and a word carries bindings —
 * address AND node — while a receipt deliberately drops the node. What
 * this seam shares with the model is the mark arithmetic and the
 * order; the full bindings are the join `log ⋈ store`, which
 * `Cas/Lang/WordWire.lean` states and a consumer performs by loading
 * each receipted address.
 *
 * ## The record is registered, never ad hoc
 *
 * Every row this seam persists and every document `since` answers is
 * spelled by the GENERATED word-wire mirrors
 * (`generated/WordLogSchema.ts`, emitted from
 * `library/cas/Cas/Lang/WordWire.lean` by `lake exe emitword`,
 * byte-identity-gated). A receipt is `(address, at, seq, size, tag)`:
 * `seq` is the mark — a zero-based word index, dense by construction —
 * and `at` is epoch milliseconds on the admitting host's clock. Time
 * is host territory (the model has no clock), and both host fields are
 * per-device honest: the word does NOT sync, so a mark and a timestamp
 * only ever speak for the store that wrote them.
 *
 * A receipt deliberately carries less than a binding: the store
 * already holds the bytes, so the log never becomes a second byte
 * plane. Every logged address is resident — the store law appends the
 * receipt only AFTER `putBytes` succeeds — so `log ⋈ load` recovers
 * full bindings whenever a consumer wants them.
 *
 * ## The page, and which realization bounds what
 *
 * `since` answers a PAGE: the suffix from the mark, at most
 * `wordLogPageLimit` receipts, with `next` meaning RESUME HERE. A
 * truncated page does not teach the tip — `next` is the mark to ask
 * from again, and only an untruncated read's `next` is the word's
 * length. The two branches are one sentence: `next` is `mark +
 * |page|` while the page is non-empty, and the word's length when it
 * is empty, so a mark past the end still answers the true cursor and a
 * client draining by `next` always advances. A bound of zero is a page
 * that cannot advance, so it is REFUSED rather than answered.
 *
 * `limit` bounds the ANSWER on every realization. It bounds the READ
 * on the sql one only, where it is a `LIMIT` clause and rows past the
 * page are never fetched or decoded. **OWED ROW — the file
 * realization's read is unbounded**: `readLog` reads and decodes the
 * whole file before the page is cut, because the corruption law below
 * is whole-log (an undecodable line anywhere but the tail refuses the
 * read). Paging the answer is therefore all `limit` can mean there,
 * and the sqlite backend is the bounded one. This is a NON-CLAIM,
 * gated so it cannot silently change: `test/WordLogPaging.test.ts`
 * asserts that a damaged line beyond the page still refuses the file
 * log, so an "optimisation" that made the file read tolerant of
 * mid-file corruption would go red.
 *
 * ## What the log records, exactly
 *
 * Fresh admissions. A duplicate put is the identity on the store and
 * appends nothing, exactly as the Lean `step` leaves the word
 * unchanged on `duplicate`. Content admitted before a store first
 * opened with this seam is present without receipts: history begins
 * when the log begins, which is the honest reading of "admission
 * order is when this store learned something".
 *
 * ## The crash direction, ruled
 *
 * Bytes first, receipt second — the same safe direction the crash
 * matrix already proves for unacknowledged puts ("durable but never
 * acknowledged"): a crash between the two leaves resident content
 * with no receipt, and the word under-reports rather than lies. The
 * reverse order could leave a receipt claiming an admission the store
 * never made, which is the one thing the store never does. A log
 * whose middle is undecodable is corruption and fails typed; only a
 * torn FINAL line of the file realization — the crash artifact — is
 * tolerated, because the put it belonged to never answered. A final
 * line that DECODES but has lost its newline is not that artifact and
 * is not dropped: see `makeFileWordLog`, where the two are told apart
 * and only one of them costs a receipt.
 */
import { Context, Effect, Layer, Option, Schema, Semaphore } from "effect"
import { FileSystem, PlatformError } from "effect"
import * as SqlClient from "effect/unstable/sql/SqlClient"
import type { SqlError } from "effect/unstable/sql/SqlError"
import { BackendFailure } from "./Backend.ts"
import { canonicalJson } from "../internal/canonicalJson.ts"
import { wordHistorySchema, wordLogEntrySchema } from "./generated/WordLogSchema.ts"

/** One receipt, in the registered spelling: the persisted record of
 * one admission. `seq` is the mark (zero-based word index), `at`
 * epoch milliseconds on the admitting host's clock. */
export type WordLogEntry = typeof wordLogEntrySchema.Type

/** The history document `since` answers: the word's suffix from a
 * mark, in admission order, and `next` — the mark of the next entry
 * to be admitted, so a client never computes its own cursor. */
export type WordHistory = typeof wordHistorySchema.Type

/** What `append` is handed: a receipt minus its mark. The log assigns
 * `seq` — atomically, in the realization's own idiom — because the
 * mark IS the log's order and a caller must not be able to claim a
 * position. */
export interface WordLogAppend {
  readonly address: string
  readonly at: number
  readonly size: number
  readonly tag: number
}

/** The word-log seam: append one receipt, read the history from a
 * mark. Like every backend seam it judges nothing — admission is the
 * store law's, and the log is only asked to remember it. */
export interface WordLogShape {
  /** Record one fresh admission. The realization assigns the mark. */
  readonly append: (
    entry: WordLogAppend,
  ) => Effect.Effect<void, BackendFailure>
  /** The word's suffix from a mark (zero-based, half-open — never a
   * timestamp), at most `limit` receipts: `since(0)` is the whole
   * history up to the page bound, an empty `word` is "nothing happened
   * since the mark". A mark past the end still answers the true
   * cursor; a negative or fractional one is floored; one that is not a
   * finite number is REFUSED rather than read as zero, because "the
   * whole history" is a different answer than the caller asked for.
   *
   * `limit` is the page bound: absent means `wordLogPageLimit`, more
   * than the cap CLAMPS to it — "at most n" is still truly answered by
   * at most the cap, and the truncation is observable through `next` —
   * and less than one is REFUSED, because a page that cannot advance
   * leaves a draining client spinning forever on a seam that keeps
   * answering it. */
  readonly since: (
    mark: number,
    limit?: number,
  ) => Effect.Effect<WordHistory, BackendFailure>
}

/** The word log in the context — the receipts seam beside the byte
 * plane and the roots registry. A composition that provides it gets a
 * store whose admissions are receipted; one that does not gets the
 * store law unchanged. */
export class WordLog extends Context.Service<WordLog, WordLogShape>()(
  "foldlab/cas/WordLog",
) {}

/** A mark off a caller: word indexes are whole and non-negative, so a
 * negative or fractional one is floored rather than reaching
 * `Array.slice`'s from-the-end reading or a SQL comparison.
 *
 * A mark that is not a finite number is not a mark at all, and is
 * REFUSED here at the library boundary. Answering `0` for it — which
 * is what a lenient floor does, since `Math.floor(NaN)` is `NaN` and
 * `NaN >= 0` is false — hands the WHOLE history to a caller who asked
 * for a position, and a seam that silently answers a different
 * question than the one it was asked is the one thing the receipts
 * plane must never do. */
const flooredMark = (mark: number): Effect.Effect<number, BackendFailure> =>
  Number.isFinite(mark)
    ? Effect.succeed(Math.max(0, Math.floor(mark)))
    : Effect.fail(new BackendFailure({
      reason: [
        `${String(mark)} is not a mark: a mark is a finite number`,
        "  a mark is a zero-based word index — a count of receipts, never a timestamp",
        "  read the whole history from mark 0, or what is new from the `next` a previous read answered",
      ].join("\n"),
    }))

/**
 * The page bound: how many receipts one `since` answers when the
 * caller names no bound, and the most it answers when the caller names
 * a larger one. ONE constant — the default and the cap are the same
 * number, so there is no second bound anywhere to drift from this one,
 * and every consumer (the route, the CLI's drain) imports it rather
 * than declaring its own.
 *
 * 10 000 receipts is the stream-loop review's parameter #11 (≈900 KB
 * of history document). Without a default the pull is unbounded and
 * `since(0)` on a large word decodes the whole log into one array;
 * without a cap a caller restores that by asking for 10⁹.
 */
export const wordLogPageLimit = 10_000

/**
 * A page bound off a caller, decoded to the bound actually served.
 *
 * Absent is the cap. Above the cap CLAMPS: `limit` means "at most n",
 * so answering at most 10 000 to a request for at most 10⁹ is a TRUE
 * answer to the question asked, and the truncation is fully observable
 * through `next` — the seam's prohibition on silently answering a
 * DIFFERENT question is not engaged, because the question's truth
 * conditions are preserved. A fractional bound floors, exactly as a
 * fractional mark does.
 *
 * Below one is REFUSED, and the reason is the drain's termination
 * argument rather than taste. A client chains `mark ← next`; the
 * variant `|w| − mark` decreases only because a non-empty page has at
 * least one receipt in it. At zero the variant never decreases and the
 * client spins forever while the seam answers it 200 every time. There
 * is no meaning-preserving clamp either — 1 answers more than was
 * asked and the cap answers vastly more — so the only honest answer is
 * a refusal that names what it refused.
 */
const boundedLimit = (
  limit: number | undefined,
): Effect.Effect<number, BackendFailure> => {
  if (limit === undefined) return Effect.succeed(wordLogPageLimit)
  const floored = Math.floor(limit)
  return Number.isFinite(floored) && floored >= 1
    ? Effect.succeed(Math.min(floored, wordLogPageLimit))
    : Effect.fail(new BackendFailure({
      reason: [
        `${String(limit)} is not a page limit: a limit is a whole count of receipts, one or more`,
        "  a page of zero cannot advance a reader — the mark it answers is the mark it was asked from, so a client draining by `next` never finishes",
        `  ask for at least 1, or leave the limit out for the default page of ${wordLogPageLimit}`,
      ].join("\n"),
    }))
}

/** The cursor a page owes, from the page it answered and the word's
 * own length — the two branches of `next`, written once so the three
 * realizations cannot disagree about them.
 *
 * While the page is non-empty the cursor is RESUME HERE (`mark +
 * |page|`), which is `|w|` exactly when the page was not truncated; an
 * empty page owes the word's end, because the mark may lie beyond it
 * and a caller who overshot must still learn where the word stops
 * rather than be handed its own out-of-range mark back. With the bound
 * at one or more the two cases are decidable from the document alone:
 * the page is empty if and only if the mark is at or past the end. */
const cursorOf = (mark: number, page: number, length: number): number =>
  page > 0 ? mark + page : length

/* ── memory ──────────────────────────────────────────────────────── */

/** One isolated in-memory word log — the test seam, and the receipts
 * half of an in-memory session. */
export const makeMemoryWordLog = (): WordLogShape => {
  const entries: Array<WordLogEntry> = []
  return {
    append: (entry) => Effect.sync(() => {
      entries.push({
        address: entry.address,
        at: entry.at,
        seq: entries.length,
        size: entry.size,
        tag: entry.tag,
      })
    }),
    since: (mark, limit) =>
      flooredMark(mark).pipe(
        Effect.flatMap((from) =>
          Effect.map(boundedLimit(limit), (bound) => {
            const word = entries.slice(from, from + bound)
            return { next: cursorOf(from, word.length, entries.length), word }
          })
        ),
      ),
  }
}

/* ── sql ─────────────────────────────────────────────────────────── */

/** The table the word lives in when the composition does not name one
 * — the receipts counterpart of `cas_objects` and `cas_roots`. */
export const defaultWordTable = "cas_word"

/** Which table the word log lives in. */
export interface SqlWordLogOptions {
  readonly table?: string
}

const sqlFailure = (error: SqlError): BackendFailure =>
  new BackendFailure({
    reason: `word log failed: ${error.message}`,
    cause: error,
  })

const decodeEntry = Schema.decodeUnknownEffect(wordLogEntrySchema)

/** The columns the receipt table has, in the registered spelling —
 * READ OFF the generated schema rather than re-typed here, so the DDL
 * below and the record cannot drift apart silently. `test/WordLog.test.ts`
 * binds them to the columns SQLite actually created. */
export const wordLogColumns: ReadonlyArray<string> = Object.keys(
  wordLogEntrySchema.fields,
)

/** The cursor aggregate, in the registered spelling: `next` decodes
 * through `wordHistorySchema`'s OWN field, so the SQL shortcut that
 * computes it and the document a client receives cannot disagree about
 * what a mark is. A bare cast would have made that agreement a
 * comment. */
const decodeCursor = Schema.decodeUnknownEffect(
  Schema.Struct({ next: wordHistorySchema.fields.next }),
)

/** One JSONL line to one receipt, in a single schema step — parse and
 * decode through the registered spelling, no bare `JSON.parse`. */
const decodeLine = Schema.decodeUnknownEffect(
  Schema.fromJsonString(wordLogEntrySchema),
)

/**
 * The word log over the `SqlClient` in context, creating the table if
 * it is not there (a composition step, exactly as the roots adapter
 * treats its own `CREATE TABLE`).
 *
 * `append` is ONE statement — `INSERT … SELECT COALESCE(MAX(seq), -1)
 * + 1` — so the mark is assigned under the same write lock that lands
 * the row: the single-statement atomic append of the root-store
 * precedent, and what keeps `seq` dense and zero-based with no
 * counter held anywhere. This is why the db-backed store needs no
 * lock file where the file realization does: the mark assignment is
 * inside the insert rather than around it.
 *
 * The DDL spells its columns with their types, so the NAMES are bound
 * to the generated record by a gate rather than by this text —
 * `wordLogColumns` is read off `wordLogEntrySchema.fields`, and
 * `test/WordLog.test.ts` asserts the table SQLite actually created
 * carries exactly those. `since` reads `WHERE seq >= mark ORDER BY
 * seq`; a row that does not decode as a receipt fails typed, because
 * order is semantics and a filtered row would silently renumber
 * history.
 */
export const makeSqlWordLog = (
  options: SqlWordLogOptions = {},
): Effect.Effect<WordLogShape, never, SqlClient.SqlClient> =>
  Effect.gen(function* () {
    // Without transforms: the columns are spelled here and in the rows
    // identically, whatever naming convention the client was
    // configured with.
    const client = (yield* SqlClient.SqlClient).withoutTransforms()
    const table = client(options.table ?? defaultWordTable)

    yield* client`
      CREATE TABLE IF NOT EXISTS ${table} (
        seq INTEGER PRIMARY KEY,
        address TEXT NOT NULL,
        tag INTEGER NOT NULL,
        size INTEGER NOT NULL,
        at INTEGER NOT NULL
      )
    `.pipe(Effect.orDie)

    const append: WordLogShape["append"] = Effect.fn("SqlWordLog.append")(
      function* (entry) {
        return yield* client`
          INSERT INTO ${table} (seq, address, tag, size, at)
          SELECT COALESCE(MAX(seq), -1) + 1, ${entry.address}, ${entry.tag},
            ${entry.size}, ${entry.at}
          FROM ${table}
        `.pipe(Effect.asVoid, Effect.mapError(sqlFailure))
      },
    )

    const since: WordLogShape["since"] = Effect.fn("SqlWordLog.since")(
      function* (mark, limit) {
        const from = yield* flooredMark(mark)
        const bound = yield* boundedLimit(limit)
        // The bound is in the STATEMENT, not in a `.slice` after it.
        // Reading the suffix and cutting it in JS answers every
        // behavioural law here and is still the unbounded read: it
        // transfers and decodes every row past the page, which is the
        // whole of the memory hazard `limit` exists to close.
        // `test/WordLogPaging.test.ts` witnesses the bound from the
        // outside — a row past the page that does not decode does not
        // refuse the page — and `test/WordLogStatement.test.ts` reads
        // the statement text itself.
        const rows = yield* client<typeof wordLogEntrySchema.Encoded>`
          SELECT seq, address, tag, size, at FROM ${table}
          WHERE seq >= ${from} ORDER BY seq LIMIT ${bound}
        `.pipe(Effect.mapError(sqlFailure))
        const word: Array<WordLogEntry> = []
        for (const row of rows) {
          // The row is still parsed at the boundary: a table is
          // external data, whatever the query's nominal type says.
          word.push(yield* decodeEntry(row).pipe(
            Effect.mapError((issue) => new BackendFailure({
              reason: `word log row is not a receipt: ${String(issue)}`,
              cause: issue,
            })),
          ))
        }
        if (word.length > 0) {
          // RESUME HERE, which is the word's end exactly when the page
          // was not truncated. Read off the page's own length rather
          // than off the last row's `seq`, so the three realizations
          // compute one formula instead of three that agree by luck.
          return { next: cursorOf(from, word.length, from), word }
        }
        // An empty page still owes the true cursor: the mark may lie
        // beyond the word, and `next` must say where the word ends.
        // This is the ONLY branch that needs the word's length, and it
        // is one aggregate row — the page above never widens to find
        // it.
        const heads = yield* client`
          SELECT COALESCE(MAX(seq), -1) + 1 AS next FROM ${table}
        `.pipe(Effect.mapError(sqlFailure))
        // Decoded, not cast: the aggregate is a database answer like
        // any other, and `next` is a mark in the registered spelling.
        const cursor = yield* decodeCursor(heads.at(0)).pipe(
          Effect.mapError((issue) => new BackendFailure({
            reason: `word log cursor is not a mark: ${String(issue)}`,
            cause: issue,
          })),
        )
        return { next: cursor.next, word }
      },
    )

    return { append, since }
  })

/* ── file ────────────────────────────────────────────────────────── */

/** The word log of a file-backed store: one append-only line file in
 * the store root, beside `objects/` and `roots/`. */
export const wordLogRelativePath = "word.jsonl"

/** The lock file that serializes appends ACROSS processes, beside the
 * log. Transient: it exists only while one writer holds the log. */
export const wordLogLockRelativePath = "word.jsonl.lock"

const isNotFound = (error: PlatformError.PlatformError): boolean =>
  error.reason._tag === "NotFound"

const isAlreadyExists = (error: PlatformError.PlatformError): boolean =>
  error.reason._tag === "AlreadyExists"

const fileFailure = (error: PlatformError.PlatformError): BackendFailure =>
  new BackendFailure({ reason: error.message, cause: error })

const utf8Encoder = new TextEncoder()

const noBytes = new Uint8Array(0)

/** How long a writer waits for the lock before refusing, as attempts
 * and the pause between them. Three seconds is far longer than any
 * append takes and far shorter than a person will wait wondering. */
const lockAttempts = 300
const lockPause = "10 millis"

/**
 * The refusal a mark out of place earns. Two defects wear the same
 * shape and must not wear the same words: a mark BEHIND its line is
 * one mark issued twice — two writers appended without the lock, and
 * both receipts are real — while a mark ahead of its line, or below
 * zero, is a line removed or renumbered by hand.
 *
 * Neither is repaired on READ. The log is the store's word: dropping
 * a duplicate would discard a receipt for content that is resident,
 * and renumbering the remainder would hand a client a history that
 * never happened. So the read refuses, names which defect it found,
 * and names the truncation that keeps every receipt still in order —
 * a repair the operator performs, because it decides what the store
 * remembers.
 */
const markOutOfOrder = (path: string, index: number, seq: number): string =>
  seq >= 0 && seq < index
    ? [
      `word log line ${index} claims mark ${seq}, which line ${seq} already holds — one mark, issued twice`,
      "  two writers appended to this log at once without the lock; both receipts are real, so neither is dropped here",
      `  the receipts before line ${index} are intact — truncate ${path} to its first ${index} lines to keep them, or open this store on the sqlite backend, which assigns the mark inside the insert`,
    ].join("\n")
    : [
      `word log line ${index} claims mark ${seq}, and marks are dense from zero — line ${index} owes mark ${index}`,
      "  a line has been removed or renumbered by hand, and order is semantics: the rest is not renumbered past it",
      `  restore ${path} from a copy, or truncate it to its first ${index} lines to keep the receipts still in order`,
    ].join("\n")

/**
 * The word log over the store root's `FileSystem` — one JSONL file,
 * each line a receipt in the registered canonical spelling, appended
 * with the platform's own append flag so a line is one write.
 *
 * ## Two writers, one mark plane
 *
 * Assigning a mark here is a read-modify-write: the mark IS the count
 * `readLog` just returned. A semaphore serializes that sequence within
 * one process; it says nothing about a second process, and two `cas
 * put`s racing in two shells would each read N and each write mark N.
 * The duplicate is not a lost update — both receipts are real — and
 * the order check below then refuses every later read, so the store's
 * history wedges on a race the store never warned about.
 *
 * So the sequence is taken under a LOCK FILE too, created with the
 * platform's exclusive flag (`wx` — O_CREAT|O_EXCL): the create is the
 * compare-and-swap, one syscall, no window between test and take. A
 * writer that dies holding it leaves the file behind, so the wait is
 * bounded and the refusal names the lock and the fix; silently seizing
 * a lock whose holder might still be running would be the very race
 * the lock exists to prevent. Reads take no lock — a torn read of an
 * in-flight append lands in the tolerance below.
 *
 * ## Two damaged tails, and why they are not the same tail
 *
 * One append is one write of `line + "\n"`, so a file that does not
 * end in a newline ends in a partial write. There are two of those,
 * and reading them alike destroys receipts.
 *
 * A final line that does not DECODE is a torn write: the put it
 * belonged to never answered, so under-reporting it is the crash
 * matrix's safe direction, and the next append truncates it away. An
 * undecodable line anywhere else IS corruption and fails typed.
 *
 * A final line that DECODES but has no newline after it is a
 * different artifact. No proper prefix of a canonical receipt is
 * valid JSON — every one of them ends mid-token or mid-object — so
 * decoding is proof that the record's bytes are all present and only
 * the separator is missing. That receipt is real and stays read. What
 * must not happen is leaving the file that way: the next append opens
 * with the platform's append flag and would run its line straight onto
 * the unterminated one, fusing two receipts into a single undecodable
 * line — which loses the acknowledged receipt AND re-issues its mark
 * for different content, the one shape of lie a receipts plane cannot
 * tell. So the missing separator is repaired first, by the same temp +
 * rename rewrite the torn tail gets.
 *
 * No fsync is asserted, the same honest posture the byte plane keeps
 * (crash matrix, finding c): a power loss — not a process crash — can
 * tear the final line, and the torn-line tolerance above is exactly
 * the read-side answer to it.
 */
export const makeFileWordLog = (
  storeRoot: string,
): Effect.Effect<WordLogShape, never, FileSystem.FileSystem> =>
  Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const writing = yield* Semaphore.make(1)
    const path = `${storeRoot}/${wordLogRelativePath}`
    const lockPath = `${storeRoot}/${wordLogLockRelativePath}`

    /** The log as read: the decoded receipts, the clean prefix they
     * spell, and the two ways the file's tail can differ from it.
     *
     * `torn` — the final line is not a receipt: the crash artifact of
     * an append whose put never answered, so under-reporting it is the
     * crash matrix's safe direction. `unterminated` — the file's last
     * receipt has no newline after it: nothing is missing from the
     * record, only its separator, so the receipt is kept.
     *
     * Either one means the bytes on disk are not `cleanPrefix`, and
     * `append` must make them so before it writes. `since` tolerates
     * both and repairs neither. */
    const readLog: Effect.Effect<
      {
        readonly entries: Array<WordLogEntry>
        readonly cleanPrefix: string
        readonly torn: boolean
        readonly unterminated: boolean
      },
      BackendFailure
    > = Effect.gen(function* () {
      const raw = yield* fs.readFileString(path).pipe(
        Effect.catchTag("PlatformError", (error) => isNotFound(error)
          ? Effect.succeed("")
          : Effect.fail(fileFailure(error))),
      )
      // An append writes the newline in the same call as the line, so
      // a file that does not end in one ends in a partial write. Which
      // KIND of partial write is settled by whether the line decodes,
      // below — not by this flag, which only says the separator is
      // missing and the file must be rewritten before it grows.
      const unterminated = raw !== "" && !raw.endsWith("\n")
      const lines = raw.split("\n")
      // A trailing newline leaves one empty tail; drop it before the
      // torn-line reading below, so a clean file has no "torn" line.
      if (lines.at(-1) === "") lines.pop()
      const entries: Array<WordLogEntry> = []
      let cleanPrefix = ""
      for (const [index, line] of lines.entries()) {
        // One schema step parses the line and decodes the receipt —
        // the ratified JSON codec discipline, no bare JSON.parse.
        const parsed = decodeLine(line).pipe(
          Effect.mapError((issue) => new BackendFailure({
            reason: `word log line ${index} is not a receipt: ${String(issue)}`,
            cause: issue,
          })),
        )
        // Only the FINAL line may fail to decode — the torn tail.
        // Anywhere else an undecodable line is corruption and the
        // typed failure propagates.
        const entry = index === lines.length - 1
          ? yield* parsed.pipe(Effect.option)
          : Option.some(yield* parsed)
        if (Option.isNone(entry)) {
          return { entries, cleanPrefix, torn: true, unterminated }
        }
        if (entry.value.seq !== index) {
          return yield* new BackendFailure({
            reason: markOutOfOrder(path, index, entry.value.seq),
          })
        }
        entries.push(entry.value)
        // Every receipt is spelled with its separator here, so the
        // clean prefix is well-formed even when the file is not — it
        // is what the repair writes.
        cleanPrefix = `${cleanPrefix}${line}\n`
      }
      return { entries, cleanPrefix, torn: false, unterminated }
    })

    const platformFailure = <A>(
      effect: Effect.Effect<A, PlatformError.PlatformError>,
    ): Effect.Effect<A, BackendFailure> => Effect.mapError(effect, fileFailure)

    /** Take the cross-process lock, or wait for it. `wx` is
     * O_CREAT|O_EXCL: the create IS the compare-and-swap. Only an
     * already-taken lock is waited on — any other platform failure is
     * this store's own and travels immediately. */
    const takeLock = (
      remaining: number,
    ): Effect.Effect<void, BackendFailure> =>
      fs.writeFile(lockPath, noBytes, { flag: "wx" }).pipe(
        Effect.catchTag("PlatformError", (error) => {
          if (!isAlreadyExists(error)) return Effect.fail(fileFailure(error))
          if (remaining === 0) {
            return Effect.fail(new BackendFailure({
              reason: [
                `another writer holds this store's word log and did not release it: ${lockPath}`,
                "  a store's appends take turns, and this one waited three seconds for its turn",
                "  if no other cas process is running, that lock is stale: remove the file and retry",
              ].join("\n"),
            }))
          }
          return Effect.flatMap(
            Effect.sleep(lockPause),
            () => takeLock(remaining - 1),
          )
        }),
      )

    /** One append, with the log's write turn already held. */
    const appendHeld = Effect.fn("FileWordLog.appendHeld")(
      function* (entry: WordLogAppend) {
        const log = yield* readLog
        if (log.torn || log.unterminated) {
          // Make the file BE the clean prefix before appending, for
          // either damage. A torn line left in place would sit mid-file
          // after this append and poison every later read as
          // corruption; truncating it discards only an admission that
          // never acknowledged — the safe direction, made durable. A
          // missing separator left in place would be worse: this
          // append would run onto the line below it and fuse two
          // receipts into one undecodable line, so the rewrite puts
          // the newline back and every receipt survives.
          //
          // The rewrite is temp + rename — the byte plane's own
          // atomicity idiom — because an in-place rewrite would hand a
          // concurrent reader a half-written prefix, which is worse
          // than the damage being repaired.
          const repair = `${path}.repair`
          yield* fs.writeFile(
            repair,
            utf8Encoder.encode(log.cleanPrefix),
          ).pipe(platformFailure)
          yield* fs.rename(repair, path).pipe(platformFailure)
        }
        const row = Schema.encodeSync(wordLogEntrySchema)({
          address: entry.address,
          at: entry.at,
          seq: log.entries.length,
          size: entry.size,
          tag: entry.tag,
        })
        yield* fs.writeFile(path, utf8Encoder.encode(`${canonicalJson(row)}\n`), {
          flag: "a",
        }).pipe(platformFailure)
      },
    )

    const append: WordLogShape["append"] = Effect.fn("FileWordLog.append")(
      function* (entry) {
        // The permit serializes this process's writers and the lock
        // file serializes the processes; the read-modify-write that
        // assigns the mark needs both, because the mark IS the count
        // it just read. The release runs on every exit — a refused
        // append must not leave the store's history locked.
        return yield* writing.withPermits(1)(Effect.acquireUseRelease(
          takeLock(lockAttempts),
          () => appendHeld(entry),
          () => fs.remove(lockPath).pipe(Effect.ignore),
        ))
      },
    )

    const since: WordLogShape["since"] = Effect.fn("FileWordLog.since")(
      function* (mark, limit) {
        const from = yield* flooredMark(mark)
        const bound = yield* boundedLimit(limit)
        // The OWED ROW, in one line: `readLog` is whole-file, so this
        // realization's `limit` pages the ANSWER and not the READ. It
        // is not an oversight to fix here — the corruption law above
        // is whole-log, and a read that stopped at the page would stop
        // finding the mid-file damage it is required to refuse. The
        // sqlite backend is the bounded one; the non-claim is gated so
        // it cannot change silently.
        const log = yield* readLog
        const word = log.entries.slice(from, from + bound)
        return { next: cursorOf(from, word.length, log.entries.length), word }
      },
    )

    return { append, since }
  })

/* ── layers ──────────────────────────────────────────────────────── */

/** One isolated in-memory word log as a layer — the test seam's Layer
 * form. Each build is its own history. */
export const layerMemoryWordLog: Layer.Layer<WordLog> =
  Layer.sync(WordLog, makeMemoryWordLog)

/** Provide the word log over the `SqlClient` in context — the
 * db-backed store's receipts plane, in the same file as its bytes and
 * roots. */
export const layerSqlWordLog = (
  options: SqlWordLogOptions = {},
): Layer.Layer<WordLog, never, SqlClient.SqlClient> =>
  Layer.effect(WordLog, makeSqlWordLog(options))

/** Provide the word log over a store root's `FileSystem` — the file
 * store's receipts plane, one line file beside `objects/` and
 * `roots/`. */
export const layerFileWordLog = (
  storeRoot: string,
): Layer.Layer<WordLog, never, FileSystem.FileSystem> =>
  Layer.effect(WordLog, makeFileWordLog(storeRoot))
