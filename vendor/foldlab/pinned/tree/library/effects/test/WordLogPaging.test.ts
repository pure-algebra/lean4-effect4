/**
 * THE BREAKER'S BATTERY — the SEAM half of S1 / Lane A.
 *
 * Contract packet: `.staging/frontend-trunk/packets/S1-HISTORY-ROUTE.md`
 * (staged; its same-tree home is
 * `test/contracts/S1-history-route.contract.md`, owed at the
 * operator's commit). Written BEFORE any implementation exists, by a
 * process that will never implement it (`implement` skill, two-role
 * law). RED BY CONSTRUCTION: `WordLogShape.since` takes no `limit`
 * today, so every case below fails on an ASSERTION about paging.
 *
 * Companion file: `DaemonHistoryRoute.test.ts` (the route half).
 *
 * The laws, by packet name:
 *
 * - S-1  L-A1/L-A2  suffix identity, positionally; density; `next` at
 *                   BOTH branches (kills adversary A4 and A5)
 * - S-2  L-A3/L-A6f the drain chain on a FIXED word: pages concatenate,
 *                   `next` strictly increases while non-empty, the
 *                   variant terminates (kills A2). W6 licenses the
 *                   fixed-word half; the GROWTH half is PDD-6 law 2 and
 *                   is OWED — no case here asserts it.
 * - S-3  L-A4      reading is state-free, at the word and (file
 *                   realization only) at the bytes
 * - S-4  L-A6      default = cap = `wordLogPageLimit` = 10 000; over-cap
 *                   CLAMPS; a limit beyond the suffix answers the suffix
 * - S-5  L-A6d     `limit = 0` REFUSES typed — the §13.2 stuck window,
 *                   refused because the drain's variant needs L ≥ 1
 * - S-6  L-A12     the three realizations agree (the α-commutation
 *                   square across memory / sqlite / file)
 * - S-7  L-A13     BG-1a: a sqlite row BEYOND the page that does not
 *                   decode does NOT refuse the page — the witness that
 *                   the decode is bounded (kills A1, QE-A2's OOM)
 * - S-8  L-A13     BG-1b: a file line beyond the page that does not
 *                   decode DOES refuse — the file realization pages the
 *                   ANSWER, not the READ, and its corruption law stays
 *                   whole-log. The owed row, gated as a NON-CLAIM.
 *
 * ## Why the casts
 *
 * A breaker's battery predates the types it names. `since` is called
 * with two arguments and `wordLogPageLimit` is read off the module
 * namespace, both through casts, so that this file fails on its
 * ASSERTIONS ("the page is 5 long, expected 2") rather than on its
 * IMPORTS ("no exported member") — a red import is a harness error and
 * says nothing about the contract. The casts stay correct after the
 * implementation lands; nothing here needs editing, and the
 * implementer may not edit it in any case.
 */
import { SqliteClient } from "@effect/sql-sqlite-bun"
import { expect, it } from "@effect/vitest"
import { Effect, FileSystem } from "effect"
import * as SqlClient from "effect/unstable/sql/SqlClient"
import { Cas } from "../src/index.ts"
import * as WordLogModule from "../src/cas/WordLog.ts"
import { withStoreRoot } from "./fixtures/diskFs.ts"

/* ── the shims the packet names ──────────────────────────────────── */

/** `WordLogShape.since` under contract: the mark, and a page bound.
 * The cast is explained in this file's header. */
type PagedSince = (
  mark: number,
  limit?: number,
) => Effect.Effect<Cas.WordHistory, Cas.BackendFailure>

const since = (log: Cas.WordLogShape): PagedSince =>
  log.since as unknown as PagedSince

/** The ONE exported cap constant the packet pins (L-A6a). Read off the
 * namespace so its absence is an assertion failure, not an import
 * failure. */
const declaredCap = (WordLogModule as unknown as Record<string, unknown>)[
  "wordLogPageLimit"
]

/** The cap the rest of this file computes with. `10_000` is the
 * stream-loop review's parameter #11; if the export disagrees, S-4a
 * says so directly. */
const cap = 10_000

/* ── one word, three carriers ────────────────────────────────────── */

/** A receipt to append. `address` is a plausible 64-hex string; the
 * record only requires a string, and the identity under test is the
 * MARK arithmetic, not the digest. */
const receipt = (index: number): Cas.WordLogAppend => ({
  address: String(index).padStart(64, "0"),
  at: 1_700_000_000_000 + index,
  size: index + 1,
  tag: index % 7,
})

/** Fill a log with `count` receipts, in order. */
const fill = (
  log: Cas.WordLogShape,
  count: number,
): Effect.Effect<void, Cas.BackendFailure> =>
  Effect.forEach(
    Array.from({ length: count }, (_unused, index) => index),
    (index) => log.append(receipt(index)),
    { discard: true },
  )

/** The word this battery reasons about, as the test's own value — the
 * independent side of L-A1. If the seam and this array disagree, the
 * seam is wrong; the test never asks the seam what the word is. */
const expectedWord = (count: number, from: number, take: number) =>
  Array.from({ length: count }, (_unused, index) => index)
    .slice(from, from + take)

const memoryLog = (
  count: number,
): Effect.Effect<Cas.WordLogShape, Cas.BackendFailure> =>
  Effect.suspend(() => {
    const log = Cas.makeMemoryWordLog()
    return Effect.as(fill(log, count), log)
  })

/** The sqlite realization over a real database file, with its client
 * kept in hand — S-7 needs to damage a row behind the seam's back. */
const withSqlLog = <A, E>(
  count: number,
  use: (
    log: Cas.WordLogShape,
    client: SqlClient.SqlClient,
  ) => Effect.Effect<A, E, FileSystem.FileSystem>,
): Effect.Effect<A, E | Cas.BackendFailure | unknown> =>
  withStoreRoot((root) =>
    Effect.gen(function* () {
      const client = yield* SqlClient.SqlClient
      const log = yield* Cas.makeSqlWordLog()
      yield* fill(log, count)
      return yield* use(log, client)
    }).pipe(Effect.provide(SqliteClient.layer({ filename: `${root}/cas.db` }))))

/** The file realization over a real store root, with the log's path —
 * S-3 and S-8 both read and damage the JSONL directly. */
const withFileLog = <A, E>(
  count: number,
  use: (
    log: Cas.WordLogShape,
    path: string,
  ) => Effect.Effect<A, E, FileSystem.FileSystem>,
): Effect.Effect<A, E | Cas.BackendFailure | unknown> =>
  withStoreRoot((root) =>
    Effect.gen(function* () {
      const log = yield* Cas.makeFileWordLog(root)
      yield* fill(log, count)
      return yield* use(log, `${root}/${Cas.wordLogRelativePath}`)
    }))

/** The outcome of a read, as one readable line — so "it answered when
 * it should have refused" is a legible assertion failure rather than a
 * serialized schema tree. A refusal is marked `REFUSED:`; an answer is
 * marked in a way that cannot be mistaken for one. */
const outcomeOf = <A>(
  effect: Effect.Effect<A, Cas.BackendFailure>,
): Effect.Effect<string> =>
  Effect.match(effect, {
    onFailure: (failure) => `REFUSED: ${failure.reason}`,
    onSuccess: (value) => `ANSWERED ${JSON.stringify(value)} — no refusal`,
  })

/** The same, projected to just the marks a page carried. */
const pageOf = (
  effect: Effect.Effect<Cas.WordHistory, Cas.BackendFailure>,
): Effect.Effect<string> =>
  Effect.match(effect, {
    onFailure: (failure) => `REFUSED: ${failure.reason}`,
    onSuccess: (page) =>
      `seqs=${page.word.map((entry) => entry.seq).join(",")} next=${page.next}`,
  })

/* ── S-1 — L-A1/L-A2: suffix identity, positionally ──────────────── */

it.effect("S-1 the page at a mark is the word's suffix, position for position, and `next` answers both branches", () =>
  Effect.gen(function* () {
    const count = 7
    const log = yield* memoryLog(count)

    // Every mark that matters: 0 (W2, the whole history), an interior
    // one, the last, exactly the frontier, and past the end.
    for (const mark of [0, 1, count - 1, count, count + 3]) {
      const page = yield* since(log)(mark, cap)
      const expected = expectedWord(count, mark, count)

      // Positional, not set-wise: a page re-sorted by `at` or by
      // `address` passes a set assertion and fails this one
      // (adversary A5; the §13.1 wrong-witness shape).
      expect(page.word.map((entry) => entry.size - 1)).toEqual(expected)
      expect(page.word.map((entry) => entry.seq)).toEqual(expected)

      // L-A2: density is answered, never renumbered.
      page.word.forEach((entry, index) => {
        expect(entry.seq).toBe(mark + index)
      })

      // L-A1: an untruncated read answers the true cursor at BOTH
      // branches. `next = m + |page|` always (adversary A4) hands a
      // caller who overshot its own out-of-range mark back, and it
      // never learns where the word ends.
      expect(page.next).toBe(count)
    }
  }))

/* ── S-2 — L-A3/L-A6f: the drain composes, and terminates ────────── */

/** Drain a FIXED word by chaining pulls. Bounded by construction: a
 * chain that does not advance is the defect under test, never a hang. */
const drain = (
  log: Cas.WordLogShape,
  from: number,
  limit: number,
): Effect.Effect<ReadonlyArray<Cas.WordHistory>, Cas.BackendFailure> =>
  Effect.gen(function* () {
    const pages: Array<Cas.WordHistory> = []
    let mark = from
    for (let step = 0; step < 64; step += 1) {
      const page = yield* since(log)(mark, limit)
      pages.push(page)
      if (page.word.length === 0) break
      if (page.next <= mark) break
      mark = page.next
    }
    return pages
  })

it.effect("S-2 chained pulls on a fixed word concatenate to the suffix, advance strictly, and drain", () =>
  Effect.gen(function* () {
    const count = 7
    const limit = 3
    const log = yield* memoryLog(count)
    const pages = yield* drain(log, 0, limit)

    // Four pulls: [0,3) [3,6) [6,7) and the empty one at the frontier.
    // An implementation that ignores `limit` answers the whole suffix
    // in one page and this is where it says so.
    expect(pages.map((page) => page.word.length)).toEqual([3, 3, 1, 0])

    // W6 `since_compose`, at the host: the concatenation IS the word.
    // No gap, no overlap, no duplicate.
    const drained = pages.flatMap((page) => page.word.map((entry) => entry.seq))
    expect(drained).toEqual(expectedWord(count, 0, count))

    // The variant: `next` strictly increases while the page is
    // non-empty, so `|w| - mark` decreases and the chain terminates.
    // A `next` pinned to the tip (adversary A2) makes the SECOND pull
    // empty and silently skips receipts 3..6.
    const marks = pages.map((page) => page.next)
    expect(marks).toEqual([3, 6, 7, 7])

    // The truncated page must NOT teach the tip (TP-17).
    expect(pages[0]!.next).toBe(3)
    expect(pages[0]!.next).not.toBe(count)
  }))

it.effect("S-2b the same chain drains identically on sqlite and on the file log", () =>
  Effect.gen(function* () {
    const count = 7
    const limit = 3
    const shape = (pages: ReadonlyArray<Cas.WordHistory>) => ({
      lengths: pages.map((page) => page.word.length),
      marks: pages.map((page) => page.next),
      seqs: pages.flatMap((page) => page.word.map((entry) => entry.seq)),
    })

    const sql = yield* withSqlLog(count, (log) => drain(log, 0, limit))
    const file = yield* withFileLog(count, (log) => drain(log, 0, limit))

    expect(shape(sql)).toEqual({
      lengths: [3, 3, 1, 0],
      marks: [3, 6, 7, 7],
      seqs: expectedWord(count, 0, count),
    })
    expect(shape(file)).toEqual(shape(sql))
  }))

/* ── S-3 — L-A4: reading is state-free ───────────────────────────── */

it.effect("S-3 a pull changes nothing: repeated pulls agree, and the file log's bytes are untouched", () =>
  withFileLog(5, (log, path) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const before = yield* fs.readFileString(path)

      const first = yield* since(log)(1, 2)
      const second = yield* since(log)(1, 2)
      // W1's second half: the answer is a function of the word alone.
      expect(second).toEqual(first)

      // Drain the whole log, twice, at several marks and bounds — no
      // read may move the word.
      yield* drain(log, 0, 2)
      yield* since(log)(0, cap)
      yield* since(log)(99, 1)

      const whole = yield* since(log)(0, cap)
      expect(whole.word.map((entry) => entry.seq)).toEqual([0, 1, 2, 3, 4])
      expect(whole.next).toBe(5)

      // The claim at the BYTES, on the realization where it is
      // meaningful: SQLite may legitimately touch -wal/-shm on a read
      // connection, so the byte-level assertion is the file log's and
      // the word-level assertion is everyone's (packet L-A4, judgment
      // call).
      const after = yield* fs.readFileString(path)
      expect(after).toBe(before)
    })))

/* ── S-4 — L-A6: the default, the cap, the clamp ─────────────────── */

it.effect("S-4a the cap is ONE exported constant and it is 10 000 receipts", () => {
  // Stream-loop review parameter #11: "`/history` page limit — 10⁴
  // receipts (≈900 KB)". TP-17: without a default the pull is
  // unbounded; without a cap `limit=10^9` restores it.
  expect(declaredCap).toBe(cap)
  return Effect.void
})

it.effect("S-4b the default page IS the cap, and a limit over the cap clamps rather than refusing", () =>
  Effect.gen(function* () {
    const count = cap + 1
    const log = yield* memoryLog(count)

    // No `limit` at all: the seam's own default bounds it. This is the
    // whole of QE-A2 — an unbounded default is the OOM.
    const byDefault = yield* since(log)(0)
    expect(byDefault.word.length).toBe(cap)
    expect(byDefault.next).toBe(cap)
    expect(byDefault.next).not.toBe(count)

    // Over the cap CLAMPS and answers 'here is a page, resume at
    // `next`'. Refusing instead would kill the only client the route
    // exists for; answering cap+1 rows would restore the unbounded
    // pull. Both directions are the falsifier.
    const overCap = yield* since(log)(0, cap + 5)
    expect(overCap.word.length).toBe(cap)
    expect(overCap.next).toBe(cap)

    const absurd = yield* since(log)(0, 1_000_000_000)
    expect(absurd.word.length).toBe(cap)
  }), 60_000)

it.effect("S-4c a limit beyond the suffix answers the suffix — unpadded, unrefused", () =>
  Effect.gen(function* () {
    const log = yield* memoryLog(4)
    const page = yield* since(log)(2, 500)
    expect(page.word.map((entry) => entry.seq)).toEqual([2, 3])
    expect(page.next).toBe(4)
  }))

/* ── S-5 — L-A6d: the stuck window is refused, not answered ──────── */

it.effect("S-5 `limit = 0` refuses typed — a page that cannot advance is not a page", () =>
  Effect.gen(function* () {
    const log = yield* memoryLog(4)

    // §13.2's stuck window: the drain's variant `|w| - mark` does not
    // decrease, so a client looping on `next` spins forever while the
    // seam keeps answering it. There is no meaning-preserving clamp
    // (1 answers more than asked; the cap answers vastly more), so the
    // seam refuses — the same posture `flooredMark` takes on a mark
    // that is not a mark.
    for (const bound of [0, -1, Number.NaN]) {
      const outcome = yield* outcomeOf(since(log)(0, bound))
      expect(outcome, `limit=${String(bound)} must refuse, not answer`)
        .toContain("REFUSED:")
      // The refusal names what it refused — a diagnostic that does not
      // reach a person is the defect `CliHistory.test.ts` already
      // stands guard over.
      expect(outcome).toContain("limit")
    }

    // A fractional bound floors, exactly as a fractional mark does —
    // the seam's existing leniency, extended consistently.
    const floored = yield* since(log)(0, 2.7)
    expect(floored.word.map((entry) => entry.seq)).toEqual([0, 1])
  }))

/* ── S-6 — L-A12: the three realizations agree ───────────────────── */

it.effect("S-6 memory, sqlite and file answer the SAME page for every (mark, limit) — the α-commutation square", () =>
  Effect.gen(function* () {
    const count = 6
    const grid: ReadonlyArray<readonly [number, number]> = [
      [0, 1],
      [0, 4],
      [2, 3],
      [5, 2],
      [6, 2],
      [9, 2],
    ]

    const probe = (log: Cas.WordLogShape) =>
      Effect.forEach(grid, ([mark, limit]) =>
        Effect.map(since(log)(mark, limit), (page) => ({
          mark,
          limit,
          next: page.next,
          seqs: page.word.map((entry) => entry.seq),
          addresses: page.word.map((entry) => entry.address),
        })))

    const memory = yield* Effect.flatMap(memoryLog(count), probe)
    const sql = yield* withSqlLog(count, probe)
    const file = yield* withFileLog(count, probe)

    // Agreement alone would be satisfied by three identically WRONG
    // realizations, so the square is pinned to its expected corner
    // first (the §1.4 determinism-assumed-not-granted shape, applied
    // to a cross-carrier claim).
    expect(memory.map((row) => ({ next: row.next, seqs: row.seqs }))).toEqual([
      { next: 1, seqs: [0] },
      { next: 4, seqs: [0, 1, 2, 3] },
      { next: 5, seqs: [2, 3, 4] },
      { next: 6, seqs: [5] },
      { next: 6, seqs: [] },
      { next: 6, seqs: [] },
    ])

    // `limit` is being written THREE times (TP-5). Three hand-written
    // paging implementations never held to each other is the standard
    // way this defect ships.
    expect(sql).toEqual(memory)
    expect(file).toEqual(memory)
  }))

/* ── S-7 — L-A13 BG-1a: the sql read is BOUNDED ──────────────────── */

it.effect("S-7 a sqlite row beyond the page that is not a receipt does not refuse the page — the bound gate", () =>
  withSqlLog(6, (log, client) =>
    Effect.gen(function* () {
      // Damage a row the page must never reach. SQLite's INTEGER
      // affinity leaves a non-numeric string as TEXT, so this row no
      // longer decodes through `wordLogEntrySchema`.
      yield* client`UPDATE cas_word SET at = 'not a mark' WHERE seq = 4`.pipe(
        Effect.orDie,
      )

      // A page of two from mark 0 must be rows 0 and 1 and nothing
      // else. Surviving the damaged row at seq 4 is the WITNESS that
      // rows beyond the page were never decoded — QE-A2's OOM is
      // exactly "every row is schema-decoded into a JS array".
      // Adversary A1 (unbounded SELECT, then `.slice(0, L)`) passes
      // every other case in this battery and fails here.
      const bounded = yield* pageOf(since(log)(0, 2))
      expect(
        bounded,
        "BG-1a: a page that refuses because a row BEYOND it did not decode is an UNBOUNDED read",
      ).toBe("seqs=0,1 next=2")

      // And the damage is still real: a page that REACHES it refuses,
      // typed. A bounded read is not a tolerant one.
      const reached = yield* pageOf(since(log)(3, 4))
      expect(reached).toContain("not a receipt")
    })))

/* ── S-8 — L-A13 BG-1b: the file read is WHOLE-LOG, by law ───────── */

it.effect("S-8 a damaged line beyond the page still refuses the FILE log — `limit` pages the answer, not the read", () =>
  withFileLog(6, (log, path) =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      // THE GUARD: this case is green both before and after the
      // implementation — it gates a NON-CLAIM. Without a baseline it
      // would pass while saying nothing, so the page bound is asserted
      // on the UNDAMAGED log first.
      const clean = yield* since(log)(0, 2)
      expect(clean.word.map((entry) => entry.seq)).toEqual([0, 1])

      const lines = (yield* fs.readFileString(path)).trimEnd().split("\n")
      expect(lines).toHaveLength(6)

      // Line 4 is NOT the final line, so this is corruption rather
      // than the tolerated torn tail.
      lines[4] = "{\"not\":\"a receipt\"}"
      yield* fs.writeFileString(path, `${lines.join("\n")}\n`)

      // The mirror image of S-7, and it is the OWED ROW made
      // executable (TP-5). `makeFileWordLog.readLog` reads the whole
      // file and refuses mid-file corruption by a RULED law
      // ("Anywhere else an undecodable line is corruption and the
      // typed failure propagates"). So the file realization's `limit`
      // bounds the ANSWER and not the READ, and the sqlite backend is
      // the bounded one. Gating the non-claim stops a later
      // "optimisation" from turning the file log into one that
      // silently tolerates corruption.
      const refusal = yield* pageOf(since(log)(0, 2))
      expect(refusal).toContain("word log line 4 is not a receipt")
    })))
