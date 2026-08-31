/**
 * THE BREAKER'S BATTERY — the ROUTE half of S1 / Lane A.
 *
 * Contract packet: `.staging/frontend-trunk/packets/S1-HISTORY-ROUTE.md`
 * (staged; its same-tree home is
 * `test/contracts/S1-history-route.contract.md`, owed at the
 * operator's commit). Written BEFORE any implementation exists, by a
 * process that will never implement it (`implement` skill, two-role
 * law). RED BY CONSTRUCTION: `GET /history` does not exist, so it
 * falls to the wildcard and cas-http/0 answers 400 from its status
 * table — every case below fails on an ASSERTION about the route.
 *
 * Companion file: `WordLogPaging.test.ts` (the seam half).
 *
 * The laws, by packet name:
 *
 * - R-1   L-A1/L-A2  the body at a mark is the word's suffix,
 *                    positionally; `next` at BOTH branches
 * - R-2   L-A3       the route-drained chain composes on a fixed word
 *                    (W6's half; PDD-6 law 2's growth half stays OWED
 *                    and is deliberately NOT asserted)
 * - R-3   L-A4       reading is state-free: identical pulls are
 *                    byte-identical and the word does not move
 * - R-4   L-A5       TWO REGISTERS: route-drained, assembled BY THE
 *                    TEST, byte-identical to one real `cas history
 *                    --json` child process. The transports differ by
 *                    construction, so the gate cannot compare the CLI
 *                    to itself (TP-16)
 * - R-5   L-A6       default = cap; over-cap clamps; limit=0 refuses;
 *                    a limit beyond the suffix answers the suffix
 * - R-6   L-A7       the door DECODES: `/^(0|[1-9][0-9]*)$/`, ≤ 2^53−1,
 *                    everything else 400 — never a coercion
 * - R-7   L-A8       the address-not-value line as a FAIL-CLOSED door:
 *                    any query key outside {since, limit} is refused,
 *                    so a silently-ignored `?tag=` cannot ship
 * - R-8   L-A9       `planeOf` claims it: `plane=history` in the request
 *                    log, and refusals wear the plane's media type
 *                    instead of going out octet-bare with no body
 * - R-9   L-A10      200 on an empty word (never 404); 405 from the
 *                    CO-TENANT on the wrong method (never the profile's
 *                    400); 403 unchanged for a foreign Origin
 * - R-10  L-A11      the wire is FROZEN: exactly {next, word} and
 *                    exactly the five receipt fields. No `hasMore`
 * - R-11  L-A14      ETag is CUT (TP-12) — asserted as the cut, not as
 *                    a judgment that validators are wrong
 * - R-12  L-A15      the record moves with the route: `historyPath`,
 *                    the banner, the drift gate, SERVING.md, PROFILE §14
 *
 * ## Why the casts
 *
 * `historyPath` is read off the module namespace so this file fails on
 * its ASSERTIONS rather than on its IMPORTS — a red import is a harness
 * error and says nothing about the contract. The cast stays correct
 * after the export lands; nothing here needs editing, and the
 * implementer may not edit it in any case.
 *
 * ## Harness
 *
 * `bootDaemon` / `withSqliteStore` are respelled from
 * `DaemonHttp.test.ts` rather than imported — that file exports
 * neither, and a breaker may not edit an existing test to make its own
 * battery convenient. A named duplication, owed to a shared daemon-test
 * fixture the way `bin/cli/history.ts` names its own respelling.
 */
import { expect, it } from "@effect/vitest"
import {
  Effect,
  FileSystem,
  Layer,
  Logger,
  Option,
  Path,
  PlatformError,
  Schema,
  Scope,
} from "effect"
import { Cas } from "../src/index.ts"
import { canonicalJson } from "../src/cas/Value.ts"
import { wordHistorySchema } from "../src/cas/generated/WordLogSchema.ts"
import { defaultServePolicy, initStore, layerCasAt } from "../bin/cli/store.ts"
import * as DaemonHttp from "../bin/mcp/http.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"

/* ── the shims and the pins the packet names ─────────────────────── */

/** The route, pinned by the packet. Used literally in every fetch, so
 * the probes work whether or not the export exists yet; R-12a asserts
 * the export separately. */
const historyRoute = "/history"

/** The plane label the packet pins for `planeOf`. */
const historyPlane = "history"

/** The exported route constant (L-A15). Read off the namespace so its
 * absence is an assertion failure, not an import failure. */
const declaredHistoryPath = (DaemonHttp as unknown as Record<string, unknown>)[
  "historyPath"
]

/** The page cap (L-A6a), stream-loop review parameter #11. */
const cap = 10_000

const casBin = new URL("../bin/cas.ts", import.meta.url).pathname

/* ── booting one daemon over one seeded store ────────────────────── */

interface DaemonHandle {
  readonly baseUrl: string
  readonly logsNow: () => ReadonlyArray<string>
}

/** One in-process daemon on an ephemeral port; the bound address is
 * read off the banner, the same line an operator reads. Respelled from
 * `DaemonHttp.test.ts` — see this file's header. */
const bootDaemon = (options: {
  readonly store: string
  readonly allowedOrigins?: ReadonlyArray<string>
}): Effect.Effect<DaemonHandle, never, Scope.Scope> =>
  Effect.gen(function* () {
    const logs: Array<string> = []
    const layerCapture = Logger.layer([
      Logger.map(Logger.formatLogFmt, (line: string) => {
        logs.push(line)
      }),
    ])
    yield* Effect.forkScoped(
      Effect.never.pipe(
        Effect.provide(
          DaemonHttp.layerDaemon({
            policy: defaultServePolicy,
            host: "127.0.0.1",
            port: Option.some(0),
            otlp: Option.none(),
            replicaTarget: Option.none(),
            allowedOrigins: options.allowedOrigins ?? [],
            allowedHosts: [],
          }).pipe(
            Layer.provideMerge(layerCasAt(options.store, "sqlite")),
            Layer.provideMerge(layerCapture),
            Layer.provideMerge(Layer.merge(layerDiskFs, Path.layer)),
          ),
        ),
      ),
    )
    const baseUrl = yield* Effect.promise(async () => {
      const deadline = Date.now() + 15_000
      for (;;) {
        const banner = logs.find((line) => line.includes("message=\"daemon serving\""))
        const dialable = banner?.match(/address=(http:\/\/[^\s]+)/u)?.[1]
        if (dialable !== undefined) return dialable
        if (Date.now() > deadline) {
          throw new Error(`the daemon never bannered; logs:\n${logs.join("\n")}`)
        }
        await new Promise((resolve) => setTimeout(resolve, 10))
      }
    })
    return { baseUrl, logsNow: () => [...logs] }
  })

/** One fresh SQLite store per probe, created the way `cas init` creates
 * it. Respelled from `DaemonHttp.test.ts`. */
const withSqliteStore = <A, E>(
  use: (store: string) => Effect.Effect<
    A,
    E,
    FileSystem.FileSystem | Path.Path | Scope.Scope
  >,
): Effect.Effect<A, E | PlatformError.PlatformError> =>
  Effect.scoped(Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const root = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-history-" })
    const store = `${root}/store`
    yield* initStore(store, true, "sqlite").pipe(Effect.orDie)
    return yield* use(store)
  })).pipe(Effect.provide(Layer.merge(layerDiskFs, Path.layer)))

/**
 * Seed the store's WORD before the daemon opens it — through
 * `Cas.Store`, the admission door that receipts.
 *
 * NOT through `PUT /cas/{hex}`: the cas-http/0 wire plane's core
 * requires `ByteReader | ByteWriter | RootStore | AddressScheme` and
 * never `WordLog` (`src/server/Core.ts:51,71-73`), so a wire PUT admits
 * bytes with no receipt. That is an OPEN ROW in the packet, outside
 * this slice; this battery does not depend on it either way.
 */
const seedWord = (
  store: string,
  count: number,
): Effect.Effect<
  ReadonlyArray<string>,
  never,
  FileSystem.FileSystem | Scope.Scope
> =>
  Effect.gen(function* () {
    const cas = yield* Cas.Store
    const addresses: Array<string> = []
    for (let index = 0; index < count; index += 1) {
      addresses.push(yield* cas.put(Cas.NodeInput.make({
        kind: { version: 0, tag: 1 },
        payload: Uint8Array.from([index, index + 1]),
        refs: [],
      })))
    }
    return addresses as ReadonlyArray<string>
  }).pipe(
    Effect.provide(layerCasAt(store, "sqlite")),
    Effect.scoped,
    Effect.orDie,
  )

/* ── the route, as a client sees it ──────────────────────────────── */

interface Answer {
  readonly status: number
  readonly body: string
  readonly headers: Record<string, string>
}

const get = (
  baseUrl: string,
  query: string,
  init?: RequestInit,
): Effect.Effect<Answer> =>
  Effect.promise(async () => {
    const response = await fetch(`${baseUrl}${historyRoute}${query}`, init)
    const headers: Record<string, string> = {}
    response.headers.forEach((value, key) => {
      headers[key.toLowerCase()] = value
    })
    return { status: response.status, body: await response.text(), headers }
  })

/** A history document as the route answered it, parsed but NOT decoded
 * — R-10 asks about the KEYS, and `Schema.decodeUnknown` strips excess
 * properties, which would answer the wrong question. */
const parsed = (answer: Answer): {
  readonly next: number
  readonly word: ReadonlyArray<Record<string, unknown>>
} => JSON.parse(answer.body) as {
  readonly next: number
  readonly word: ReadonlyArray<Record<string, unknown>>
}

/** The route drained by chaining pulls — the CLIENT's loop, written
 * here and nowhere else, so R-4 cannot compare production code to
 * itself. Bounded by construction: a chain that does not advance is
 * the defect under test, never a hang. */
const drainRoute = (
  baseUrl: string,
  from: number,
  limit: number,
): Effect.Effect<ReadonlyArray<Answer>> =>
  Effect.gen(function* () {
    const pages: Array<Answer> = []
    let mark = from
    for (let step = 0; step < 64; step += 1) {
      const answer = yield* get(baseUrl, `?since=${mark}&limit=${limit}`)
      pages.push(answer)
      if (answer.status !== 200) break
      const page = parsed(answer)
      if (page.word.length === 0) break
      if (page.next <= mark) break
      mark = page.next
    }
    return pages
  })

/** One real `cas history --json --since m` process, for the OTHER
 * register. A child process, not a harness call: the two sides of L-A5
 * must differ in transport. */
const cliHistoryJson = (store: string, mark: number): Effect.Effect<string> =>
  Effect.promise(async () => {
    const child = Bun.spawn(
      ["bun", casBin, "history", "--json", "--since", String(mark), "--store", store],
      { stdout: "pipe", stderr: "pipe" },
    )
    const out = await new Response(child.stdout).text()
    await child.exited
    return out.trimEnd()
  })

/** A file beside this test, read through the `FileSystem` service —
 * the same discipline `ServingDoc.test.ts` uses on its own subject. */
const docAt = (
  relative: string,
): Effect.Effect<string, never, FileSystem.FileSystem | Path.Path> =>
  Path.Path.pipe(
    Effect.flatMap((path) => path.fromFileUrl(new URL(relative, import.meta.url))),
    Effect.flatMap((file) =>
      FileSystem.FileSystem.pipe(Effect.flatMap((fs) => fs.readFileString(file)))
    ),
    Effect.orDie,
  )

const layerFiles: Layer.Layer<FileSystem.FileSystem | Path.Path> = Layer.merge(
  layerDiskFs,
  Path.layer,
)

/* ── R-1 — L-A1/L-A2: the body IS the suffix ─────────────────────── */

it.live("R-1 the route answers the word's suffix at a mark, position for position, with `next` at both branches", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      const count = 7
      const addresses = yield* seedWord(store, count)
      const handle = yield* bootDaemon({ store })

      for (const mark of [0, 1, count - 1, count, count + 3]) {
        const answer = yield* get(handle.baseUrl, `?since=${mark}`)
        expect(answer.status, `GET ${historyRoute}?since=${mark}`).toBe(200)
        const page = parsed(answer)
        const expected = addresses.slice(Math.min(mark, count))

        // Positional, not set-wise: a page re-sorted by `at` or by
        // `address` (adversary A5) passes a set assertion and fails
        // this one.
        expect(page.word.map((entry) => entry["address"])).toEqual(expected)
        page.word.forEach((entry, index) => {
          expect(entry["seq"]).toBe(mark + index)
        })

        // Past the end still answers the TRUE CURSOR — the seam's
        // standing sentence. `next = mark + |page|` always (adversary
        // A4) hands an overshooting caller its own mark back.
        expect(page.next, `next at mark ${mark}`).toBe(count)
      }
    })), 60_000)

/* ── R-2 — L-A3: the drained chain composes on a fixed word ──────── */

it.live("R-2 chained pulls over HTTP concatenate to the suffix, advance strictly, and drain", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      const count = 7
      const addresses = yield* seedWord(store, count)
      const handle = yield* bootDaemon({ store })

      const pages = yield* drainRoute(handle.baseUrl, 0, 3)
      expect(
        pages.map((answer) => answer.status),
        "every pull in the chain must answer 200",
      ).toEqual(pages.map(() => 200))
      const documents = pages.map(parsed)

      // Four pulls: [0,3) [3,6) [6,7) and the empty one at the
      // frontier. A route that ignores `limit` answers everything in
      // one page and says so here.
      expect(documents.map((page) => page.word.length)).toEqual([3, 3, 1, 0])

      // W6 `since_compose` at the host: the concatenation IS the
      // suffix — no gap, no overlap, no duplicate. The GROWTH half
      // (PDD-6 law 2) is OWED and is deliberately not asserted: the
      // word is frozen for the whole chain.
      expect(documents.flatMap((page) => page.word.map((entry) => entry["address"])))
        .toEqual(addresses)

      // The variant: `next` strictly increases while the page is
      // non-empty. A `next` pinned to the tip (adversary A2) makes the
      // second pull empty and silently skips receipts 3..6.
      expect(documents.map((page) => page.next)).toEqual([3, 6, 7, 7])

      // A truncated page does NOT teach the tip (TP-17).
      expect(documents[0]!.next).toBe(3)
      expect(documents[0]!.next).not.toBe(count)
    })), 60_000)

/* ── R-3 — L-A4: reading is state-free ───────────────────────────── */

it.live("R-3 a pull changes nothing: identical pulls are byte-identical and the word does not move", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      const count = 5
      yield* seedWord(store, count)
      const handle = yield* bootDaemon({ store })

      const first = yield* get(handle.baseUrl, "?since=1&limit=2")
      const second = yield* get(handle.baseUrl, "?since=1&limit=2")
      expect(first.status).toBe(200)
      // BYTE identity, not value equality: a route whose key order
      // wanders (adversary A6) is not answering one document.
      expect(second.body).toBe(first.body)

      // Read the word every way it can be read, then ask again.
      yield* drainRoute(handle.baseUrl, 0, 2)
      yield* get(handle.baseUrl, "?since=0")
      yield* get(handle.baseUrl, "?since=99")

      const whole = yield* get(handle.baseUrl, "?since=0")
      expect(parsed(whole).next).toBe(count)
      expect(parsed(whole).word.length).toBe(count)
    })), 60_000)

/* ── R-4 — L-A5: two registers, one document ─────────────────────── */

it.live("R-4 the route drained is byte-identical to one `cas history --json` process — two registers, one document", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      const count = 7
      yield* seedWord(store, count)
      const handle = yield* bootDaemon({ store })

      // (a) The UNTRUNCATED read, with no assembly at all: the route's
      //     raw bytes ARE the CLI's line. This is the strongest form of
      //     the two-register law and the one that kills adversary A6.
      for (const mark of [0, 3, 7]) {
        const answer = yield* get(handle.baseUrl, `?since=${mark}`)
        expect(answer.status).toBe(200)
        const cli = yield* cliHistoryJson(store, mark)
        expect(answer.body, `route vs CLI at mark ${mark}`).toBe(cli)
      }

      // (b) The TRUNCATED drain, assembled BY THIS TEST — never by
      //     shared production code, so the gate cannot compare the CLI
      //     to itself (TP-16's worry, closed by construction).
      const pages = yield* drainRoute(handle.baseUrl, 0, 2)
      const documents = pages.map(parsed)
      const assembled = canonicalJson(Schema.encodeSync(wordHistorySchema)(
        Schema.decodeUnknownSync(wordHistorySchema)({
          next: documents[documents.length - 1]!.next,
          word: documents.flatMap((page) => page.word),
        }),
      ))
      const cli = yield* cliHistoryJson(store, 0)
      expect(assembled).toBe(cli)
    })), 90_000)

/* ── R-5 — L-A6: the default, the cap, the clamp, the zero ───────── */

it.live("R-5 the route's bounds: a default page, an over-cap clamp, a refused zero, a limit past the suffix", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      const count = 4
      yield* seedWord(store, count)
      const handle = yield* bootDaemon({ store })

      // No `limit`: the seam's default bounds it. On a small word that
      // is the whole word — the cap itself is gated at the seam
      // (WordLogPaging S-4), and the route inherits it through the ONE
      // exported constant.
      const byDefault = yield* get(handle.baseUrl, "?since=0")
      expect(byDefault.status).toBe(200)
      expect(parsed(byDefault).word.length).toBe(count)

      // Over the cap CLAMPS rather than refusing: `limit` means "at
      // most n", so answering at most 10 000 is a TRUE answer to a
      // request for at most 10^9, and the truncation is observable
      // through `next`. Refusing here would kill the only client the
      // route exists for.
      const absurd = yield* get(handle.baseUrl, `?since=0&limit=${cap * 100}`)
      expect(absurd.status, "an over-cap limit clamps; it does not refuse").toBe(200)
      expect(parsed(absurd).word.length).toBe(count)

      // A limit beyond the suffix answers the suffix — unpadded.
      const beyond = yield* get(handle.baseUrl, "?since=2&limit=50")
      expect(beyond.status).toBe(200)
      expect(parsed(beyond).word.length).toBe(2)
      expect(parsed(beyond).next).toBe(count)

      // Zero is the §13.2 stuck window: the drain's variant does not
      // decrease, so a looping client spins forever while the route
      // keeps answering 200. There is no meaning-preserving clamp.
      const zero = yield* get(handle.baseUrl, "?since=0&limit=0")
      expect(zero.status, "limit=0 must refuse, not answer an empty page").toBe(400)
    })), 60_000)

/* ── R-6 — L-A7: the door decodes, it does not coerce ────────────── */

it.live("R-6 the door decodes a mark from a string and refuses everything that is not one", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      yield* seedWord(store, 3)
      const handle = yield* bootDaemon({ store })

      // Absent `since` is mark 0 — the whole history (W2).
      const bare = yield* get(handle.baseUrl, "")
      expect(bare.status).toBe(200)
      expect(parsed(bare).word.length).toBe(3)

      // The accepted set is the CANONICAL decimal encodings of ℕ, one
      // string per mark. At the wire the input is a string, so this is
      // a decode, not a coercion — the seam's leniency (`flooredMark`)
      // exists for a caller who already holds a `number` and is
      // untouched by this ruling.
      for (
        const bad of [
          "-1",
          "1.5",
          "1e3",
          "+1",
          "%201",
          "0x10",
          "01",
          "",
          "abc",
          "NaN",
          "Infinity",
          "9007199254740993",
        ]
      ) {
        const answer = yield* get(handle.baseUrl, `?since=${bad}`)
        expect(answer.status, `?since=${bad} must refuse, never coerce`).toBe(400)
      }

      for (const bad of ["-1", "1.5", "abc", "", "1e3"]) {
        const answer = yield* get(handle.baseUrl, `?limit=${bad}`)
        expect(answer.status, `?limit=${bad} must refuse`).toBe(400)
      }
    })), 60_000)

/* ── R-7 — L-A8: the address-not-value line, fail-closed ─────────── */

it.live("R-7 the route refuses every query key outside {since, limit} — the door, not the behaviour", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      yield* seedWord(store, 3)
      const handle = yield* bootDaemon({ store })

      // THE GUARD, and it is load-bearing: while the route is absent
      // EVERY request answers 400 from the wildcard's status table, so
      // the refusals below would pass for the wrong reason — the
      // §1.1 sampling-as-proof defect, in a battery. The baseline must
      // answer 200 before a refusal means anything.
      const baseline = yield* get(handle.baseUrl, "?since=0&limit=2")
      expect(baseline.status, "the refusals below only discriminate once the route answers")
        .toBe(200)

      // QE-A3, as adopted: word-INDEX arithmetic is safe; receipt-FIELD
      // predicates are not. §6's seed ("no parameter filters by receipt
      // field") is PREDICATE TOO WEAK — an implementation that silently
      // IGNORES `?tag=1` satisfies it while being strictly worse, since
      // the client believes it received a filtered answer and folds a
      // lie. The contract is therefore the DOOR.
      for (
        const key of [
          "tag",
          "address",
          "column",
          "size",
          "at",
          "kind",
          "q",
          "filter",
          "from",
          "to",
          "etag",
        ]
      ) {
        const answer = yield* get(handle.baseUrl, `?since=0&${key}=1`)
        expect(answer.status, `?${key}= must be refused, never ignored`).toBe(400)
      }

      // `from`/`to` are refused on SCOPE, not on capability (TP-7):
      // `since+limit` already IS a ranged read. Lifting the refusal is
      // a ruling, not an implementation choice.
      const window = yield* get(handle.baseUrl, "?from=0&to=2")
      expect(window.status).toBe(400)
    })), 60_000)

/* ── R-8 — L-A9: the plane claims it, so refusals have a body ────── */

it.live("R-8 `planeOf` claims the route: the request log says plane=history and refusals wear JSON, not silence", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      yield* seedWord(store, 2)
      const handle = yield* bootDaemon({ store })

      yield* get(handle.baseUrl, "?since=0")
      const line = handle.logsNow().find((entry) =>
        entry.includes("message=request") && entry.includes(`path=${historyRoute}`)
      )
      expect(line, "the route logged no request line").toBeDefined()
      expect(line).toContain(`plane=${historyPlane}`)
      expect(line).not.toContain("plane=cas-http/0")

      // An unextended `planeOf` answers "cas-http/0", and
      // `refusedResponse` then goes OCTET-BARE: the operator sees a
      // naked 400 and the client sees nothing. The doc chore and the
      // correctness of the refusal surface are one edit.
      const refused = yield* get(handle.baseUrl, "?since=nonsense")
      expect(refused.status).toBe(400)
      expect(refused.body.length, "a refusal on this plane must carry its clause").toBeGreaterThan(0)
      const clause = JSON.parse(refused.body) as Record<string, unknown>
      expect(Object.keys(clause).sort()).toEqual(["fix", "refused", "why"])

      // The front door's own refusal takes the same branch, so it is
      // the same claim from the other side.
      const foreign = yield* get(handle.baseUrl, "?since=0", {
        headers: { origin: "http://not-allowed.example" },
      })
      expect(foreign.status).toBe(403)
      expect(foreign.body.length, "an origin refusal on this plane must carry its clause")
        .toBeGreaterThan(0)
    })), 60_000)

/* ── R-9 — L-A10: status discipline under PROFILE §14 ────────────── */

it.live("R-9 an empty word is 200, the wrong method is the co-tenant's 405, a foreign Origin is still 403", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      // No seeding: the word is empty, which is a FACT and not a
      // missing resource. A 404 here would make "no history yet"
      // indistinguishable from "no route" — the confusion SPEC §3.2
      // forbids.
      const handle = yield* bootDaemon({ store })

      const empty = yield* get(handle.baseUrl, "?since=0")
      expect(empty.status).toBe(200)
      expect(parsed(empty)).toEqual({ next: 0, word: [] })

      // PROFILE §14: the profile's status table "does not answer
      // exchanges inside a declared co-tenant prefix", and §14's /mcp
      // row shows the shape — 405 on the wrong method is the
      // co-tenant's, never the profile's 400.
      for (const method of ["POST", "PUT", "DELETE"]) {
        const answer = yield* get(handle.baseUrl, "?since=0", { method })
        expect(answer.status, `${method} ${historyRoute} must be the co-tenant's 405`)
          .toBe(405)
      }

      // The security posture is unchanged: a browser on another origin
      // still needs --allow-origin.
      const foreign = yield* get(handle.baseUrl, "?since=0", {
        headers: { origin: "http://not-allowed.example" },
      })
      expect(foreign.status).toBe(403)
      expect(foreign.headers["access-control-allow-origin"]).toBeUndefined()
    })), 60_000)

/* ── R-10 — L-A11: the wire is frozen ────────────────────────────── */

it.live("R-10 the document is exactly the registered record — no `hasMore`, no `total`, no tip", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      yield* seedWord(store, 5)
      const handle = yield* bootDaemon({ store })

      // A TRUNCATED page is where a "more remains" field would be
      // invented. TP-17: v1 needs none — the face count is the fold's.
      // Adding one is an emitter change in `WordWire.lean` plus a byte
      // gate, i.e. a different slice.
      const answer = yield* get(handle.baseUrl, "?since=0&limit=2")
      expect(answer.status).toBe(200)
      const document = parsed(answer)
      expect(Object.keys(document).sort()).toEqual(["next", "word"])
      expect(document.word.length).toBe(2)
      for (const entry of document.word) {
        expect(Object.keys(entry).sort())
          .toEqual(["address", "at", "seq", "size", "tag"])
      }

      // And it decodes through the GENERATED mirror, unchanged.
      const decoded = Schema.decodeUnknownSync(wordHistorySchema)(document)
      expect(decoded.next).toBe(2)
    })), 60_000)

/* ── R-11 — L-A14: ETag is cut ───────────────────────────────────── */

it.live("R-11 no validator ships in this slice — ETag is CUT, and a conditional request is answered in full", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      yield* seedWord(store, 3)
      const handle = yield* bootDaemon({ store })

      // TP-12 cut it: unruled, mis-scoped to closed ranges, and its
      // correctness premise is falsified by the log's own truncation
      // repair — `markOutOfOrder` instructs the operator to TRUNCATE,
      // after which `next` moves backward and a cached validator is
      // stale-but-fresh-looking. This asserts the CUT, not a judgment
      // that validators are wrong; TP-12 leaves the door open to a
      // correctly scoped slice later.
      const answer = yield* get(handle.baseUrl, "?since=0")
      expect(answer.status).toBe(200)
      expect(answer.headers["etag"]).toBeUndefined()
      expect(answer.headers["last-modified"]).toBeUndefined()

      const conditional = yield* get(handle.baseUrl, "?since=0", {
        headers: { "if-none-match": "\"3\"" },
      })
      expect(conditional.status).toBe(200)
      expect(conditional.body).toBe(answer.body)
    })), 60_000)

/* ── R-12 — L-A15: the record moves with the route ───────────────── */

it.live("R-12 the route is visible to the export, the banner, the drift gate, SERVING.md and PROFILE §14", () =>
  withSqliteStore((store) =>
    Effect.gen(function* () {
      // (a) ONE exported constant, so nothing hand-types the path.
      expect(declaredHistoryPath, "bin/mcp/http.ts must export historyPath")
        .toBe(historyRoute)

      // (b) The startup banner: the one line an agent reads to know
      //     what this process is.
      const handle = yield* bootDaemon({ store })
      const banner = handle.logsNow().find((line) =>
        line.includes("message=\"daemon serving\"")
      )
      expect(banner).toContain(`history=${historyRoute}`)

      // (c) The drift gate must be able to SEE the fourth route.
      //     `ServingDoc.test.ts` re-derives its route table from the
      //     named exports, so a route it does not name goes stale in
      //     both documents, silently, forever after. The extension of
      //     that gate is itself contract (TP-16).
      const driftGate = yield* docAt("./ServingDoc.test.ts")
      expect(driftGate, "ServingDoc.test.ts's route set must name historyPath")
        .toContain("historyPath")

      // (d) SERVING.md's route table.
      const serving = yield* docAt("../SERVING.md")
      expect(serving).toContain(`\`${historyRoute}\``)

      // (e) PROFILE-CAS-HTTP-0 §14's co-tenant table, additive at /0
      //     exactly as decision 32(c) ruled for the other three.
      const profile = yield* docAt("../PROFILE-CAS-HTTP-0.md")
      expect(profile).toContain(`\`${historyRoute}\``)
      expect(profile, "§14 still says the daemon declares three co-tenants")
        .not.toContain("declares three")
    }).pipe(Effect.provide(layerFiles))), 60_000)
