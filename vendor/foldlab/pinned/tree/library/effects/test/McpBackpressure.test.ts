/**
 * BS-1 — "the host cannot stall silently", as a standing regression
 * suite.
 *
 * These are the backend-robustness audit's own probes, reconstructed
 * from its probe table and run against a real SQLite store on disk.
 * Each names the hazard it stands for, because a passing assertion
 * whose hazard has been forgotten is a test nobody can maintain:
 *
 * 1. OVERSIZE. The audit's 4 MiB payload against a 1 MiB cap was
 *    correctly refused; its 64 MiB payload produced
 *    `MaxBufferSizeExceeded`, logged twice at ERROR, and NO REPLY AT
 *    ALL — the request was lost, not refused, and a client without a
 *    timeout waits for it forever. Here: an over-cap call must come
 *    back as an `mcp/NodeTooLarge` refusal, and — the sharper claim —
 *    a payload the POLICY ITSELF permits must never be one the
 *    transport loses. The unclamped case is exercised beside the
 *    clamped one, so the regression is visible as a difference and not
 *    only as an assertion.
 * 2. BURST. The audit fired 5000 concurrent puts and watched resident
 *    memory go 82 MB → 310 MB — about 46 KB per in-flight request,
 *    with nothing bounding the count. Here: a burst against a
 *    deliberately small `maxInFlight`, and the in-flight gauge must
 *    never exceed it while every request is still answered. The same
 *    burst with the bound raised shows the bound is what holds it.
 * 3. HEAD OF LINE. The audit held a SQLite write lock from another
 *    process for four seconds and watched `tools/list` — which touches
 *    no database at all — wait the whole time, with no log line for six
 *    seconds. Here: the same hold, from a real second process, in two
 *    halves. Reads taken under the hold must be answered while it is
 *    held. And the case BS-1 does NOT fix — the host's own write
 *    meeting the lock, which stops the event loop outright — must be
 *    REPORTED: a late heartbeat and a `cas.store.sql_wait` that
 *    carries the wait. "Cannot stall silently" is the claim; "cannot
 *    stall" would be a different change and is not made here.
 * 4. HEARTBEAT. The stall detector itself. A missing or late line IS
 *    the signal, so the assertion is that the lines arrive on period
 *    and carry the gap they measured.
 *
 * The host boots the way `McpHost.test.ts` boots it — a real stdio
 * session over `Stdio.layerTest`, against a temp store. Nothing calls
 * a handler directly: every number below came out of the protocol.
 */
import { describe, expect, it } from "@effect/vitest"
import {
  Deferred,
  Duration,
  Effect,
  Fiber,
  FileSystem,
  Layer,
  Logger,
  Metric,
  Path,
  PlatformError,
  Schema,
  Sink,
  Stdio,
  Stream,
} from "effect"
import { Cas } from "../src/index.ts"
import {
  casDatabaseName,
  defaultMaxInFlight,
  defaultServePolicy,
  initStore,
  layerCasAt,
  type ServePolicy,
  StoreConfig,
} from "../bin/cli/store.ts"
import {
  applyServePolicy,
  frameSlackBytes,
  type HostLimits,
  layerServeStdio,
  maxServableNodeBytes,
  transportFrameBytes,
} from "../bin/mcp/server.ts"
import * as Telemetry from "../bin/mcp/telemetry.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"

const encoder = new TextEncoder()
const decoder = new TextDecoder()

interface JsonRpcFrame {
  readonly id?: number
  readonly result?: Record<string, unknown>
  readonly error?: Record<string, unknown>
}

/** What one probe hands back: the frames the client saw, the wall
 * clock at which each id was answered, and every log line the host
 * wrote while it ran. */
interface Transcript {
  readonly frames: ReadonlyArray<JsonRpcFrame>
  readonly answeredAt: ReadonlyMap<number, number>
  readonly logs: ReadonlyArray<string>
}

const handshake: ReadonlyArray<unknown> = [
  {
    jsonrpc: "2.0",
    id: 1,
    method: "initialize",
    params: {
      protocolVersion: "2025-06-18",
      capabilities: {},
      clientInfo: { name: "foldlab-bs1", version: "0" },
    },
  },
  { jsonrpc: "2.0", method: "notifications/initialized" },
]

const call = (id: number, name: string, args: Record<string, unknown>): unknown => ({
  jsonrpc: "2.0",
  id,
  method: "tools/call",
  params: { name, arguments: args },
})

const putCall = (id: number, payloadHex: string): unknown =>
  call(id, "cas_put", {
    version: Cas.SchemeVersion,
    tag: 1,
    payload: payloadHex,
    refs: [],
  })

/** Requests as the bytes a client writes: one JSON document per line. */
const framesOf = (requests: ReadonlyArray<unknown>): Stream.Stream<Uint8Array> =>
  Stream.fromIterable(
    requests.map((request) => encoder.encode(`${JSON.stringify(request)}\n`)),
  )

/**
 * One probe against a booted host.
 *
 * Four things it does that `McpHost.test.ts`'s helper does not, each
 * for a probe: the frames are TIMED as they arrive (head-of-line is a
 * question about when, not whether); the host's own logfmt lines are
 * captured rather than dropped (the heartbeat probe reads them); the
 * limits are a parameter (the burst probe needs a bound small enough to
 * reach); and stdin is a caller-built `Stream`, so a probe can hold a
 * request back until something else has happened.
 */
const probe = (
  options: {
    readonly store: string
    readonly limits: HostLimits
    readonly stdin: Stream.Stream<Uint8Array>
    readonly awaitIds: ReadonlyArray<number>
    readonly timeout: Duration.Duration
    readonly alongside?: Effect.Effect<void>
  },
): Effect.Effect<Transcript, never, Path.Path> =>
  Effect.gen(function* () {
    const written: Array<string> = []
    const logs: Array<string> = []
    const answeredAt = new Map<number, number>()

    const layerStdio = Stdio.layerTest({
      stdin: options.stdin.pipe(Stream.concat(Stream.never)),
      stdout: () =>
        Sink.forEach((chunk: string | Uint8Array) =>
          Effect.sync(() => {
            written.push(typeof chunk === "string" ? chunk : decoder.decode(chunk))
          })
        ),
      stderr: () => Sink.drain,
    })

    // The host's logfmt lines, captured instead of printed. The format
    // is the one `cas serve` installs, so the heartbeat probe reads
    // exactly the bytes an operator would read.
    const layerCapture = Logger.layer([
      Logger.map(Logger.formatLogFmt, (line: string) => {
        logs.push(line)
      }),
    ])

    const frames = (): ReadonlyArray<JsonRpcFrame> =>
      written
        .join("")
        .split("\n")
        .filter((line) => line.length > 0)
        .map((line) => JSON.parse(line) as JsonRpcFrame)

    const noteArrivals = (): void => {
      const now = Date.now()
      for (const frame of frames()) {
        if (frame.id !== undefined && !answeredAt.has(frame.id)) {
          answeredAt.set(frame.id, now)
        }
      }
    }

    // One provide over one composed layer (not a provide chain): each
    // later layer feeds everything before it, outputs merged — the
    // same resolution order the former chain had, with one lifecycle.
    const server = yield* Effect.forkChild(
      Effect.never.pipe(
        Effect.provide(layerServeStdio(options.limits).pipe(
          Layer.provideMerge(layerCasAt(options.store, "sqlite")),
          Layer.provideMerge(layerStdio),
          Layer.provideMerge(layerCapture),
          Layer.provideMerge(layerDiskFs),
        )),
      ),
    )
    const beside = options.alongside === undefined
      ? undefined
      : yield* Effect.forkChild(options.alongside)

    const deadline = Date.now() + Duration.toMillis(options.timeout)
    for (;;) {
      noteArrivals()
      if (options.awaitIds.every((id) => answeredAt.has(id))) break
      if (Date.now() > deadline) break
      yield* Effect.sleep("2 millis")
    }
    noteArrivals()

    if (beside !== undefined) yield* Fiber.interrupt(beside)
    yield* Fiber.interrupt(server)
    return { frames: frames(), answeredAt, logs }
  })

/** One fresh SQLite store per probe, created the way `cas init`
 * creates it — the config `init` writes is part of what is under
 * test. */
const withSqliteStore = <A, E>(
  use: (store: string) => Effect.Effect<A, E, FileSystem.FileSystem | Path.Path>,
): Effect.Effect<A, E | PlatformError.PlatformError> =>
  Effect.scoped(Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const root = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-bs1-" })
    const store = `${root}/store`
    yield* initStore(store, true, "sqlite").pipe(Effect.orDie)
    return yield* use(store)
  })).pipe(Effect.provide(Layer.merge(layerDiskFs, Path.layer)))

const replyTo = (transcript: Transcript, id: number): JsonRpcFrame | undefined =>
  transcript.frames.find((frame) => frame.id === id)

const refusedWith = (frame: JsonRpcFrame | undefined): string =>
  JSON.stringify(frame?.result ?? {})

/** A policy scaled so the probes reach their own bounds cheaply. */
const tightPolicy: ServePolicy = {
  ...defaultServePolicy,
  maxInFlight: 8,
  maxNodeBytes: 1024,
}

const hexOf = (bytes: number): string => "ab".repeat(bytes)

/* ── 0. the frame cap, as arithmetic ─────────────────────────────── */

describe("BS-1 — the frame-cap discipline (ruling R1(b))", () => {
  it("keeps this host's own cap firing before the transport's", () => {
    // Two hex characters per payload byte, plus the document around
    // it. This inequality is the whole discipline.
    expect(maxServableNodeBytes * 2 + frameSlackBytes).toBeLessThanOrEqual(
      transportFrameBytes,
    )
    // Pinned against the transport, which builds its NDJSON parser
    // with no options and therefore takes this default.
    expect(transportFrameBytes).toBe(16 * 1024 * 1024)
  })

  it.effect("clamps a policy that would let the transport lose a request", () =>
    Effect.gen(function* () {
      const reckless: ServePolicy = {
        ...defaultServePolicy,
        maxNodeBytes: 64 * 1024 * 1024,
      }
      const limits = yield* applyServePolicy(reckless)
      expect(limits.maxNodeBytes).toBe(maxServableNodeBytes)
      expect(limits.maxNodeBytes * 2 + frameSlackBytes)
        .toBeLessThanOrEqual(transportFrameBytes)
    }))

  it.effect("leaves a policy inside the cap exactly as written", () =>
    Effect.gen(function* () {
      const limits = yield* applyServePolicy(defaultServePolicy)
      expect(limits.maxNodeBytes).toBe(defaultServePolicy.maxNodeBytes)
      expect(limits.maxInFlight).toBe(defaultServePolicy.maxInFlight)
    }))
})

describe("BS-1 — ServePolicy.maxInFlight (ruling R2)", () => {
  it.effect("a store whose config predates the field is served under the default", () =>
    Effect.gen(function* () {
      // Exactly what `cas init` wrote before BS-1: no `maxInFlight`
      // key at all. Adding a REQUIRED field would have made every such
      // store undecodable, so the key is optional on the wire and
      // defaulted on decode.
      const legacy = JSON.stringify({
        backend: "sqlite",
        serve: {
          port: 8080,
          maxBatchKeys: 64,
          maxNodeBytes: 1_048_576,
          anonymousReads: true,
        },
      })
      const decoded = yield* Schema.decodeUnknownEffect(
        Schema.fromJsonString(StoreConfig),
      )(legacy)
      expect(decoded.serve?.maxInFlight).toBe(defaultMaxInFlight)
    }))

  it.effect("a store initialized today says what it is served under", () =>
    Effect.gen(function* () {
      const written = yield* Schema.encodeEffect(Schema.fromJsonString(StoreConfig))(
        StoreConfig.make({ backend: "sqlite", serve: defaultServePolicy }),
      )
      expect(written).toContain(`"maxInFlight":${defaultMaxInFlight}`)
    }))
})

/* ── 1. oversize ─────────────────────────────────────────────────── */

describe("BS-1 probe — OVERSIZE", () => {
  it.live("an over-cap payload is refused with its clause, and the session survives", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const limits = yield* applyServePolicy(tightPolicy)
        const transcript = yield* probe({
          store,
          limits,
          stdin: framesOf([
            ...handshake,
            putCall(2, hexOf(tightPolicy.maxNodeBytes + 1)),
            putCall(3, "68656c6c6f"),
          ]),
          awaitIds: [2, 3],
          timeout: Duration.seconds(20),
        })

        // The refusal ARRIVED. That is the whole probe — the audit's
        // failure mode was silence, not a wrong answer.
        const refusal = replyTo(transcript, 2)
        expect(refusal, "the over-cap call was never answered").toBeDefined()
        expect(refusal?.result?.["isError"]).toBe(true)
        // The `mcp/NodeTooLarge` clause, in the words the client is
        // handed: the tool error carries the refusal's own message.
        expect(refusedWith(refusal)).toContain("exceeds this store's maxNodeBytes")

        // And the session is healthy afterwards.
        expect(replyTo(transcript, 3)?.result?.["isError"]).not.toBe(true)
      })
    ))

  it.live("a payload the CLAMPED policy permits is answered; one the UNCLAMPED policy permits is lost", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        // The largest node a client may send under the effective cap.
        // Its frame is the largest frame a conforming client can
        // produce, and it must survive the transport.
        const atCap = yield* Effect.sync(() => hexOf(maxServableNodeBytes))
        const clamped = yield* applyServePolicy({
          ...defaultServePolicy,
          maxNodeBytes: transportFrameBytes,
        })
        expect(clamped.maxNodeBytes).toBe(maxServableNodeBytes)

        const answered = yield* probe({
          store,
          limits: clamped,
          stdin: framesOf([...handshake, putCall(2, atCap)]),
          awaitIds: [2],
          timeout: Duration.seconds(60),
        })
        const reply = replyTo(answered, 2)
        expect(reply, "the largest conforming payload was lost").toBeDefined()
        expect(reply?.result?.["isError"]).not.toBe(true)

        // The same host WITHOUT the clamp: a policy of 16 MiB says a
        // 10 MiB node is legal, its frame is 20 MiB, and the transport
        // throws it away without ever answering. This is the audit's
        // silent loss, reproduced — and the reason the clamp exists.
        const unclamped: HostLimits = {
          maxNodeBytes: transportFrameBytes,
          maxInFlight: defaultServePolicy.maxInFlight,
        }
        const lost = yield* probe({
          store,
          limits: unclamped,
          stdin: framesOf([...handshake, putCall(2, hexOf(10 * 1024 * 1024))]),
          awaitIds: [2],
          timeout: Duration.seconds(15),
        })
        expect(
          replyTo(lost, 2),
          "the unclamped oversize frame was answered — the upstream defect may be fixed, and this probe's premise with it",
        ).toBeUndefined()
        // The handshake still went through, so the session was alive
        // the whole time: the request was lost, not the connection.
        expect(replyTo(lost, 1)).toBeDefined()
      })
    ), 120_000)
})

/* ── 2. burst ────────────────────────────────────────────────────── */

/** Watch the in-flight gauge. A gauge's final value is always zero, so
 * its peak has to be sampled while the burst runs. */
const samplePeak = (into: { peak: number }): Effect.Effect<void> =>
  Effect.gen(function* () {
    for (;;) {
      const state = yield* Metric.value(Telemetry.inflight)
      into.peak = Math.max(into.peak, Number(state.value))
      yield* Effect.sleep("1 milli")
    }
  })

describe("BS-1 probe — BURST", () => {
  it.live("in-flight never exceeds maxInFlight, and every call is still answered", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const limits = yield* applyServePolicy(tightPolicy)
        const count = 200
        const ids = Array.from({ length: count }, (_, index) => index + 2)
        const watched = { peak: 0 }

        const transcript = yield* probe({
          store,
          limits,
          stdin: framesOf([
            ...handshake,
            ...ids.map((id) => putCall(id, id.toString(16).padStart(4, "0").repeat(8))),
          ]),
          awaitIds: ids,
          timeout: Duration.seconds(60),
          alongside: samplePeak(watched),
        })

        const answered = ids.filter((id) => replyTo(transcript, id) !== undefined)
        expect(answered.length, "not every burst call was answered").toBe(count)
        // Vacuity guard: if the gauge never moved, the bound was never
        // under pressure and the assertion below would prove nothing.
        expect(watched.peak, "the in-flight gauge never moved").toBeGreaterThan(1)
        expect(
          watched.peak,
          `in-flight peaked at ${watched.peak}, above the bound of ${limits.maxInFlight}`,
        ).toBeLessThanOrEqual(limits.maxInFlight)
      })
    ), 90_000)

  it.live("the same burst without a meaningful bound runs far wider — the bound is what holds it", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const count = 200
        const ids = Array.from({ length: count }, (_, index) => index + 2)
        const watched = { peak: 0 }

        yield* probe({
          store,
          // The pre-BS-1 shape: a permit for every request there could
          // be, which is what "unbounded" amounts to.
          limits: { maxNodeBytes: 1024, maxInFlight: count * 2 },
          stdin: framesOf([
            ...handshake,
            ...ids.map((id) => putCall(id, id.toString(16).padStart(4, "0").repeat(8))),
          ]),
          awaitIds: ids,
          timeout: Duration.seconds(60),
          alongside: samplePeak(watched),
        })

        expect(
          watched.peak,
          `unbounded in-flight peaked at ${watched.peak} — no wider than the bound of ${tightPolicy.maxInFlight}, so the bounded probe proves nothing`,
        ).toBeGreaterThan(tightPolicy.maxInFlight)
      })
    ), 90_000)
})

/* ── 3. head of line ─────────────────────────────────────────────── */

/** A real second process holding the store's write lock. It has to be
 * a separate process: `bun:sqlite` is synchronous, so a hold taken in
 * THIS process would block the very event loop the probe is measuring
 * and the probe would be testing itself. */
const holdScript = `
import { Database } from "bun:sqlite"
const db = new Database(process.env.CAS_DB)
db.run("PRAGMA busy_timeout = 30000;")
db.run("BEGIN IMMEDIATE")
db.run("INSERT OR IGNORE INTO cas_roots (address) VALUES ('" + "0".repeat(64) + "')")
process.stdout.write("held\\n")
await new Promise((resolve) => setTimeout(resolve, Number(process.env.CAS_HOLD_MS)))
db.run("COMMIT")
db.close()
`

/** The audit's head-of-line setup, as a fixture: seed a node, take an
 * external write lock, then drive the host with `probed` and report
 * when each id was answered relative to the moment the lock was taken.
 * The lock is taken only AFTER the host has finished its handshake,
 * which is the audit's own sequence — a live host, then contention,
 * then requests. */
const underWriteLock = (options: {
  readonly store: string
  readonly holdMillis: number
  readonly probed: (address: string) => ReadonlyArray<unknown>
  readonly awaitIds: ReadonlyArray<number>
}) =>
  Effect.gen(function* () {
    const limits = yield* applyServePolicy(defaultServePolicy)

    const seeded = yield* probe({
      store: options.store,
      limits,
      stdin: framesOf([...handshake, putCall(2, "68656c6c6f")]),
      awaitIds: [2],
      timeout: Duration.seconds(20),
    })
    const address = (seeded.frames.find((frame) => frame.id === 2)?.result?.[
      "structuredContent"
    ] as { readonly address?: string })?.address
    expect(address, "the seed put was not answered").toBeDefined()

    const held = yield* Deferred.make<number>()
    const child = Bun.spawn(["bun", "-e", holdScript], {
      env: {
        ...process.env,
        CAS_DB: `${options.store}/${casDatabaseName}`,
        CAS_HOLD_MS: String(options.holdMillis),
      },
      stdout: "pipe",
      stderr: "inherit",
    })
    const takeHold = Effect.promise(async () => {
      const reader = child.stdout.getReader()
      const first = await reader.read()
      reader.releaseLock()
      return decoder.decode(first.value ?? new Uint8Array()).includes("held")
    }).pipe(Effect.flatMap((ok) =>
      ok
        ? Deferred.succeed(held, Date.now())
        : Effect.die("the lock holder never reported taking the lock")
    ))

    const transcript = yield* probe({
      store: options.store,
      limits,
      stdin: framesOf(handshake).pipe(
        Stream.concat(
          Stream.fromEffect(Deferred.await(held)).pipe(
            Stream.flatMap(() => framesOf(options.probed(address ?? ""))),
          ),
        ),
      ),
      awaitIds: options.awaitIds,
      timeout: Duration.millis(options.holdMillis + 8000),
      alongside: takeHold.pipe(Effect.asVoid),
    })

    const holdStarted = yield* Deferred.await(held)
    yield* Effect.promise(() => child.exited)
    return {
      transcript,
      /** How long after the lock was taken an id was answered, or
       * `undefined` if it never was. */
      after: (id: number): number | undefined => {
        const at = transcript.answeredAt.get(id)
        return at === undefined ? undefined : at - holdStarted
      },
    }
  })

describe("BS-1 probe — HEAD OF LINE", () => {
  it.live("reads are answered while another process holds the write lock", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const holdMillis = 3000
        const run = yield* underWriteLock({
          store,
          holdMillis,
          probed: (address) => [
            { jsonrpc: "2.0", id: 2, method: "tools/list" },
            call(3, "cas_load", { address }),
          ],
          awaitIds: [2, 3],
        })

        const listed = run.after(2)
        const loaded = run.after(3)
        expect(listed, "tools/list was never answered").toBeDefined()
        expect(loaded, "cas_load was never answered").toBeDefined()
        // The audit measured 4000 ms of starvation for a call that
        // touches no SQL at all. Both of these must land well inside
        // the hold, not after it.
        expect(listed!, `tools/list answered ${listed}ms into a ${holdMillis}ms hold`)
          .toBeLessThan(holdMillis)
        expect(loaded!, `cas_load answered ${loaded}ms into a ${holdMillis}ms hold`)
          .toBeLessThan(holdMillis)
      })
    ), 60_000)

  it.live("a stall this host CANNOT avoid is reported rather than silent", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        // The honest half of BS-1. When the host's OWN write meets the
        // external lock, `bun:sqlite`'s busy wait is synchronous and
        // stops the whole process: no fiber runs, no timer fires, no
        // log flushes. Measured on this machine, a 3000 ms hold delays
        // a concurrent `tools/list` by ~3012 ms whether the read path
        // has its own connection or shares the writer's — the driver's
        // semaphore is not the binding constraint when every statement
        // blocks the loop. Removing the stall is a different change
        // (the audit's R6: put SQLite behind a socket).
        //
        // What BS-1 delivers is the second half of its own name: the
        // host cannot stall SILENTLY. The heartbeat's `lateMs` and the
        // `cas.store.sql_wait` timer both have to carry the stall, and
        // that is what is asserted here.
        const holdMillis = 3000
        const run = yield* underWriteLock({
          store,
          holdMillis,
          probed: (address) => [
            putCall(2, "cafebabe"),
            { jsonrpc: "2.0", id: 3, method: "tools/list" },
            call(4, "cas_load", { address }),
          ],
          awaitIds: [2, 3, 4],
        })

        // The stall is real: this is the hazard, not a regression.
        expect(run.after(2), "the contended put was never answered").toBeDefined()
        expect(run.after(2)!).toBeGreaterThan(holdMillis / 2)

        // And it is VISIBLE. A beat that ran late is the detector's
        // whole output — the gap is the stall.
        const beats = run.transcript.logs.filter((line) => line.includes("heartbeat"))
        const late = beats
          .map((line) => Number(/lateMs=(\d+)/u.exec(line)?.[1] ?? 0))
          .reduce((worst, value) => Math.max(worst, value), 0)
        expect(
          late,
          `no beat reported a late gap — the stall was silent, which is exactly what BS-1 forbids: ${
            beats.join(" | ")
          }`,
        ).toBeGreaterThan(holdMillis / 4)

        // The SQL path's own measurement agrees with it.
        const worstSqlWait = beats
          .map((line) => Number(/cas\.store\.sql_wait[^ ]*count=\d+,max=(\d+)/u.exec(line)?.[1] ?? 0))
          .reduce((worst, value) => Math.max(worst, value), 0)
        expect(worstSqlWait, "the SQL timer did not record the wait")
          .toBeGreaterThan(holdMillis / 2)
      })
    ), 60_000)
})

/* ── 4. heartbeat ────────────────────────────────────────────────── */

describe("BS-1 — the heartbeat", () => {
  it.live("beats on period and carries the gap it measured", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const limits = yield* applyServePolicy(defaultServePolicy)
        const transcript = yield* probe({
          store,
          limits,
          stdin: framesOf([...handshake, putCall(2, "68656c6c6f")]),
          // Nothing to wait for past the put: the probe runs out its
          // timeout on purpose, so several beats fall inside it.
          awaitIds: [2, 9999],
          timeout: Duration.millis(
            Duration.toMillis(Telemetry.heartbeatInterval) * 3 + 500,
          ),
        })

        const beats = transcript.logs.filter((line) => line.includes("heartbeat"))
        expect(beats.length, "the host never beat").toBeGreaterThanOrEqual(2)
        for (const beat of beats) {
          expect(beat).toContain("lateMs=")
          expect(beat).toContain("elapsedMs=")
        }
        // The metrics ride along, which is what makes a beat worth
        // reading rather than merely counting.
        expect(beats.some((beat) => beat.includes("cas.host.calls"))).toBe(true)
      })
    ), 30_000)
})
