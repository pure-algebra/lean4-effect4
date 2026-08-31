/**
 * The daemon, probed — the crash matrix's rows as standing tests.
 *
 * `cas daemon` binds the two ratified planes on one port; these probes
 * drive it the way its clients will: over real HTTP against a real
 * SQLite store, and — for the rows the audit said must be proved on a
 * REAL process — against a spawned `bun bin/cas.ts daemon` that gets
 * SIGKILLed mid-put. Each suite names the hazard it stands for:
 *
 * 1. BOOT + SURFACES. The banner names the actual bound address, the
 *    planes, and the offered protocol revisions; all three surfaces
 *    answer; the profile's own refusals (missing profile, unknown
 *    path) come from the status table, never a router 404; the
 *    heartbeat beats on the daemon exactly as it does on stdio.
 * 2. THE WIRE PLANE'S LAW. cas-http/0's admission outcomes — 201
 *    admitted, 200 already-admitted, 409 digest mismatch, 413 over
 *    budget, publish/read on the roots space — through the first bind
 *    the transport-free core has ever had.
 * 3. MCP OVER HTTP. The same six tools, the same typed refusals, over
 *    the Streamable HTTP session flow (session id + protocol-version
 *    headers), including the oversize refusal `mcp/NodeTooLarge`.
 * 4. CROSS-PLANE WAL (crash-matrix "writer contention", multiplexed).
 *    Concurrent MCP-over-HTTP puts, cas-http/0 puts, and a REAL stdio
 *    host child on the SAME database file — every admission answers,
 *    and every answered address loads back through the full read law.
 * 5. SIGKILL MID-PUT (crash-matrix row 1, the audit's probe as a
 *    guarded test). A real daemon process killed under concurrent
 *    load; the store reopens with every acknowledged address verified
 *    by re-digest and re-decode; a fresh daemon boots on the dirty
 *    store and serves.
 * 6. REFUSE-FIRST. `anonymousReads: false` refuses the boot with its
 *    own clause — the credentialed HTTP story is a named non-goal,
 *    never a silent downgrade to open reads.
 * 7. REPLICA LAG. The gauge says `-1` and the log says why when
 *    nothing is measurable; a named local replica directory is
 *    measured as now − newest write.
 */
import { describe, expect, it } from "@effect/vitest"
import {
  Duration,
  Effect,
  Encoding,
  FileSystem,
  Layer,
  Logger,
  Metric,
  Option,
  Path,
  PlatformError,
  Scope,
} from "effect"
import { Cas } from "../src/index.ts"
import {
  defaultServePolicy,
  initStore,
  layerCasAt,
  locateStore,
  readConfig,
  StoreConfig,
  type ServePolicy,
} from "../bin/cli/store.ts"
import {
  applyDaemonPolicy,
  layerDaemon,
  layerReplicaLag,
} from "../bin/mcp/http.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"

const encoder = new TextEncoder()
const decoder = new TextDecoder()

const casBin = new URL("../bin/cas.ts", import.meta.url).pathname

const profileHeaders = { "cas-profile": "cas-http/0" }
const octetHeaders = {
  ...profileHeaders,
  "content-type": "application/octet-stream",
}

/** A canonical value node over a payload, and the scheme-0 address its
 * bytes answer to — computed CLIENT-side, which is what a cas-http/0
 * uploader must do before it can name the resource it is putting. */
const nodeOf = (
  payload: Uint8Array,
): Effect.Effect<{ readonly address: string; readonly bytes: Uint8Array }> => {
  const bytes = Cas.encodeNode({
    kind: { version: 0, tag: 1 },
    payload,
    refs: [],
  })
  return Effect.promise(() => crypto.subtle.digest("SHA-256", bytes.slice())).pipe(
    Effect.map((digest) => ({
      address: Encoding.encodeHex(new Uint8Array(digest)),
      bytes,
    })),
  )
}

/** The canonical key-list document for a leaf root: count 0, nothing
 * else — the four zero bytes §4 of the profile ratifies. */
const emptyKeyList = new Uint8Array([0, 0, 0, 0])

/* ── booting the daemon in-process ───────────────────────────────── */

interface DaemonHandle {
  readonly baseUrl: string
  readonly logsNow: () => ReadonlyArray<string>
}

/**
 * One in-process daemon over a store, on an ephemeral port. The bound
 * address is read from the BANNER — the same line an operator reads —
 * so every probe that boots this way also proves the banner names a
 * dialable address.
 */
const bootDaemon = (options: {
  readonly store: string
  readonly policy?: ServePolicy
  readonly replicaTarget?: string
  readonly allowedOrigins?: ReadonlyArray<string>
  readonly allowedHosts?: ReadonlyArray<string>
  readonly otlp?: string
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
        // One provide over one composed layer — chaining four would
        // build them under four lifecycles (effect(multipleEffectProvide)).
        Effect.provide(
          layerDaemon({
            policy: options.policy ?? defaultServePolicy,
            host: "127.0.0.1",
            port: Option.some(0),
            otlp: options.otlp === undefined
              ? Option.none()
              : Option.some(options.otlp),
            replicaTarget: options.replicaTarget === undefined
              ? Option.none()
              : Option.some(options.replicaTarget),
            allowedOrigins: options.allowedOrigins ?? [],
            allowedHosts: options.allowedHosts ?? [],
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

/** One fresh SQLite store per probe, created the way `cas init`
 * creates it. */
const withSqliteStore = <A, E>(
  use: (store: string) => Effect.Effect<A, E, FileSystem.FileSystem | Path.Path | Scope.Scope>,
): Effect.Effect<A, E | PlatformError.PlatformError> =>
  Effect.scoped(Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const root = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-daemon-" })
    const store = `${root}/store`
    yield* initStore(store, true, "sqlite").pipe(Effect.orDie)
    return yield* use(store)
  })).pipe(Effect.provide(Layer.merge(layerDiskFs, Path.layer)))

/* ── HTTP clients, one per plane ─────────────────────────────────── */

const wirePut = (
  baseUrl: string,
  payload: Uint8Array,
): Effect.Effect<{ readonly address: string; readonly status: number }> =>
  nodeOf(payload).pipe(
    Effect.flatMap(({ address, bytes }) =>
      Effect.promise(() =>
        fetch(`${baseUrl}/cas/${address}`, {
          method: "PUT",
          headers: octetHeaders,
          body: bytes.slice(),
        })
      ).pipe(Effect.map((response) => ({ address, status: response.status })))),
  )

interface McpSession {
  readonly call: (
    id: number,
    name: string,
    args: Record<string, unknown>,
  ) => Effect.Effect<{
    readonly status: number
    readonly result: Record<string, unknown> | undefined
  }>
}

/** The Streamable HTTP session flow, as a client: initialize, capture
 * the session id, send the initialized notification, then call tools
 * under the session and protocol-version headers. */
const mcpSession = (baseUrl: string): Effect.Effect<McpSession> =>
  Effect.promise(async () => {
    const jsonHeaders = {
      "content-type": "application/json",
      accept: "application/json, text/event-stream",
    }
    const initialized = await fetch(`${baseUrl}/mcp`, {
      method: "POST",
      headers: jsonHeaders,
      body: JSON.stringify({
        jsonrpc: "2.0",
        id: 1,
        method: "initialize",
        params: {
          protocolVersion: "2025-06-18",
          capabilities: {},
          clientInfo: { name: "foldlab-daemon-probe", version: "0" },
        },
      }),
    })
    const session = initialized.headers.get("mcp-session-id") ?? ""
    await initialized.text()
    const sessionHeaders = {
      ...jsonHeaders,
      "mcp-session-id": session,
      "mcp-protocol-version": "2025-06-18",
    }
    await fetch(`${baseUrl}/mcp`, {
      method: "POST",
      headers: sessionHeaders,
      body: JSON.stringify({ jsonrpc: "2.0", method: "notifications/initialized" }),
    })
    const call: McpSession["call"] = (id, name, args) =>
      Effect.promise(async () => {
        const response = await fetch(`${baseUrl}/mcp`, {
          method: "POST",
          headers: sessionHeaders,
          body: JSON.stringify({
            jsonrpc: "2.0",
            id,
            method: "tools/call",
            params: { name, arguments: args },
          }),
        })
        const body = response.status === 200
          ? (await response.json() as { result?: Record<string, unknown> }).result
          : undefined
        return { status: response.status, result: body }
      })
    return { call }
  })

/* ── 1. boot + surfaces ──────────────────────────────────────────── */

describe("daemon — boot, banner, and the three surfaces", () => {
  it.live("banners the bind and answers every surface from its own table", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const handle = yield* bootDaemon({ store })

        const banner = handle.logsNow().find((line) =>
          line.includes("message=\"daemon serving\"")
        )
        expect(banner).toContain("mcp=/mcp")
        expect(banner).toContain("metrics=/metrics")
        expect(banner).toContain("2025-11-25")
        expect(banner).toContain("heartbeatMs=2000")

        // The capability document: 200, exactly eight canonical bytes.
        const caps = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/control/capabilities`, { headers: profileHeaders })
        )
        expect(caps.status).toBe(200)
        const capBytes = new Uint8Array(yield* Effect.promise(() => caps.arrayBuffer()))
        expect(capBytes.length).toBe(8)

        // The wire law's own refusals, not the router's defaults: a
        // profile-less request and an unknown resource both answer 400
        // from the status table.
        const noProfile = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/control/capabilities`)
        )
        expect(noProfile.status).toBe(400)
        const unknown = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/nowhere`, { headers: profileHeaders })
        )
        expect(unknown.status).toBe(400)

        // The MCP endpoint is POST-only; the metrics route serves the
        // Prometheus exposition with the daemon's own sensors in it.
        const mcpGet = yield* Effect.promise(() => fetch(`${handle.baseUrl}/mcp`))
        expect(mcpGet.status).toBe(405)
        const metrics = yield* Effect.promise(async () => {
          const response = await fetch(`${handle.baseUrl}/metrics`)
          return { status: response.status, body: await response.text() }
        })
        expect(metrics.status).toBe(200)
        expect(metrics.body).toContain("cas_replica_age_ms")

        // The heartbeat discipline extends to the daemon: beats arrive
        // on period, carrying the snapshot.
        yield* Effect.sleep(Duration.millis(4500))
        const beats = handle.logsNow().filter((line) => line.includes("message=heartbeat"))
        expect(beats.length).toBeGreaterThanOrEqual(2)
        expect(beats[0]).toContain("metrics=")

        // Every exchange above logged one sequence-numbered request
        // line naming its plane.
        const requests = handle.logsNow().filter((line) => line.includes("message=request"))
        expect(requests.some((line) => line.includes("plane=cas-http/0"))).toBe(true)
        expect(requests.some((line) => line.includes("plane=metrics"))).toBe(true)
      })
    ), 30_000)
})

/* ── 2. the wire plane's law ─────────────────────────────────────── */

describe("daemon — cas-http/0 serves the admission law (the core's first bind)", () => {
  it.live("admits, re-answers, refuses, and publishes through the status table", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const handle = yield* bootDaemon({ store })
        const { address, bytes } = yield* nodeOf(encoder.encode("first-bind"))

        const put = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/cas/${address}`, {
            method: "PUT",
            headers: octetHeaders,
            body: bytes.slice(),
          })
        )
        expect(put.status).toBe(201)

        // Idempotent by identity: the same bytes again answer 200.
        const rePut = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/cas/${address}`, {
            method: "PUT",
            headers: octetHeaders,
            body: bytes.slice(),
          })
        )
        expect(rePut.status).toBe(200)

        // A body under an address it does not digest to: 409, and the
        // store is unchanged at that address.
        const wrong = address.replace(/[0-9a-f]/u, (first) =>
          first === "0" ? "1" : "0")
        const mismatch = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/cas/${wrong}`, {
            method: "PUT",
            headers: octetHeaders,
            body: bytes.slice(),
          })
        )
        expect(mismatch.status).toBe(409)

        // The read answers the exact canonical bytes the address names.
        const got = yield* Effect.promise(async () => {
          const response = await fetch(`${handle.baseUrl}/cas/${address}`, {
            headers: profileHeaders,
          })
          return {
            status: response.status,
            bytes: new Uint8Array(await response.arrayBuffer()),
          }
        })
        expect(got.status).toBe(200)
        expect(Encoding.encodeHex(got.bytes)).toBe(Encoding.encodeHex(bytes))

        // Publish the admitted node as a leaf root, then read the
        // registry fact back: 204 published, 204 present, 404 absent.
        const published = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/roots/${address}`, {
            method: "PUT",
            headers: octetHeaders,
            body: emptyKeyList.slice(),
          })
        )
        expect(published.status).toBe(204)
        const present = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/roots/${address}`, { headers: profileHeaders })
        )
        expect(present.status).toBe(204)
        const absent = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/roots/${wrong}`, { headers: profileHeaders })
        )
        expect(absent.status).toBe(404)

        // Publishing an unheld root refuses as closure-unverified.
        const unheld = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/roots/${wrong}`, {
            method: "PUT",
            headers: octetHeaders,
            body: emptyKeyList.slice(),
          })
        )
        expect(unheld.status).toBe(409)
      })
    ), 30_000)

  it.live("refuses an over-budget node with 413 — never silence", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const tight: ServePolicy = { ...defaultServePolicy, maxNodeBytes: 1024 }
        const handle = yield* bootDaemon({ store, policy: tight })
        const { address, bytes } = yield* nodeOf(new Uint8Array(4096).fill(0xab))
        const over = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/cas/${address}`, {
            method: "PUT",
            headers: octetHeaders,
            body: bytes.slice(),
          })
        )
        expect(over.status).toBe(413)
      })
    ), 30_000)
})

/* ── 3. MCP over HTTP ────────────────────────────────────────────── */

describe("daemon — MCP over HTTP is the same host", () => {
  it.live("serves the emitted tool table and the typed refusals through the session flow", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const tight: ServePolicy = { ...defaultServePolicy, maxNodeBytes: 1024 }
        const handle = yield* bootDaemon({ store, policy: tight })
        const session = yield* mcpSession(handle.baseUrl)

        // A put whose address the client can also compute: the two
        // planes agree on identity because there is one scheme.
        const payload = encoder.encode("mcp-over-http")
        const { address } = yield* nodeOf(payload)
        const put = yield* session.call(10, "cas_put", {
          version: 0,
          tag: 1,
          payload: Encoding.encodeHex(payload),
          refs: [],
        })
        expect(put.status).toBe(200)
        const answered = (put.result?.["structuredContent"] as {
          readonly address?: string
        })?.address
        expect(answered).toBe(address)

        // The node loads back on the OTHER plane: one store, two wires.
        const got = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/cas/${address}`, { headers: profileHeaders })
        )
        expect(got.status).toBe(200)

        // The oversize refusal is the host's typed clause, on this
        // transport as on stdio.
        const over = yield* session.call(11, "cas_put", {
          version: 0,
          tag: 1,
          payload: "ab".repeat(4096),
          refs: [],
        })
        expect(over.status).toBe(200)
        // The wire carries the refusal's DETAIL (the clause's own
        // sentence); the `mcp/NodeTooLarge` tag is the error's name on
        // the failure schema, and this is its sentence.
        expect(JSON.stringify(over.result)).toContain("exceeds this store's maxNodeBytes")
        expect(JSON.stringify(over.result)).toContain("\"isError\":true")

        // A load of an absent address refuses with the store's clause.
        const missing = yield* session.call(12, "cas_load", {
          address: "f".repeat(64),
        })
        expect(missing.status).toBe(200)
        expect(JSON.stringify(missing.result)).toContain("nothing in the store at")
      })
    ), 30_000)
})

/* ── 4. cross-plane WAL, multiplexed ─────────────────────────────── */

/** A stdio host child on the same store, driven over its pipe: the
 * audit proved cross-PROCESS WAL safe; this rides a real second
 * process beside the daemon's multiplexed load to prove cross-PLANE. */
const stdioPuts = (
  store: string,
  payloads: ReadonlyArray<Uint8Array>,
): Effect.Effect<ReadonlyArray<string>> =>
  Effect.promise(async () => {
    const child = Bun.spawn(["bun", casBin, "serve", "--store", store], {
      stdin: "pipe",
      stdout: "pipe",
      stderr: "ignore",
    })
    // No leaked stdio host on any exit path — killing an
    // already-exited child is a no-op.
    try {
      return await driveStdioHost(child, payloads)
    } finally {
      child.kill(9)
    }
  })

const driveStdioHost = async (
  child: Bun.Subprocess<"pipe", "pipe", "ignore">,
  payloads: ReadonlyArray<Uint8Array>,
): Promise<ReadonlyArray<string>> => {
  const handshake = [
      {
        jsonrpc: "2.0",
        id: 1,
        method: "initialize",
        params: {
          protocolVersion: "2025-06-18",
          capabilities: {},
          clientInfo: { name: "foldlab-crossplane", version: "0" },
        },
      },
      { jsonrpc: "2.0", method: "notifications/initialized" },
    ]
    const puts = payloads.map((payload, index) => ({
      jsonrpc: "2.0",
      id: 100 + index,
      method: "tools/call",
      params: {
        name: "cas_put",
        arguments: {
          version: 0,
          tag: 1,
          payload: Encoding.encodeHex(payload),
          refs: [],
        },
      },
    }))
    child.stdin.write(
      [...handshake, ...puts].map((frame) => `${JSON.stringify(frame)}\n`).join(""),
    )
    await child.stdin.flush()

    const wanted = new Set(puts.map((frame) => frame.id))
    const addresses: Array<string> = []
    const reader = child.stdout.getReader()
    let buffered = ""
    const deadline = Date.now() + 30_000
    while (wanted.size > 0 && Date.now() < deadline) {
      const chunk = await reader.read()
      if (chunk.done) break
      buffered += decoder.decode(chunk.value)
      let newline = buffered.indexOf("\n")
      while (newline >= 0) {
        const line = buffered.slice(0, newline)
        buffered = buffered.slice(newline + 1)
        newline = buffered.indexOf("\n")
        if (line.length === 0) continue
        const frame = JSON.parse(line) as {
          readonly id?: number
          readonly result?: {
            readonly structuredContent?: { readonly address?: string }
          }
        }
        if (frame.id !== undefined && wanted.has(frame.id)) {
          wanted.delete(frame.id)
          const address = frame.result?.structuredContent?.address
          if (address !== undefined) addresses.push(address)
        }
      }
    }
    reader.releaseLock()
    await child.stdin.end()
    await child.exited
    if (wanted.size > 0) {
      throw new Error(`stdio host left ${wanted.size} puts unanswered`)
  }
  return addresses
}

describe("daemon — cross-plane WAL under multiplexed load", () => {
  it.live("HTTP clients on both planes and a stdio host share one file; every ack loads back", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const handle = yield* bootDaemon({ store })
        const session = yield* mcpSession(handle.baseUrl)

        const wirePayloads = Array.from({ length: 40 }, (_, index) =>
          encoder.encode(`wire-${index}`))
        const mcpPayloads = Array.from({ length: 40 }, (_, index) =>
          encoder.encode(`mcp-${index}`))
        const stdioPayloads = Array.from({ length: 10 }, (_, index) =>
          encoder.encode(`stdio-${index}`))

        // All three clients at once, on one database file.
        const [wireAcks, mcpAcks, stdioAcks] = yield* Effect.all([
          Effect.forEach(wirePayloads, (payload) => wirePut(handle.baseUrl, payload), {
            concurrency: 16,
          }),
          Effect.forEach(mcpPayloads, (payload, index) =>
            session.call(500 + index, "cas_put", {
              version: 0,
              tag: 1,
              payload: Encoding.encodeHex(payload),
              refs: [],
            }).pipe(Effect.map((reply) =>
              (reply.result?.["structuredContent"] as {
                readonly address?: string
              })?.address
            )), { concurrency: 16 }),
          stdioPuts(store, stdioPayloads),
        ], { concurrency: "unbounded" })

        for (const ack of wireAcks) {
          expect(ack.status).toBe(201)
        }
        const answered = [
          ...wireAcks.map((ack) => ack.address),
          ...mcpAcks.map((address) => {
            expect(address).toBeDefined()
            return address ?? ""
          }),
          ...stdioAcks,
        ]
        expect(answered.length).toBe(90)

        // The full read law over every acknowledged address, through a
        // fresh composition on the same file: re-digest, re-decode,
        // known kind — nothing multiplexing lost or tore.
        const verified = yield* Effect.forEach(answered, (address) =>
          Cas.Loader.pipe(
            Effect.flatMap((loader) => loader.load(Cas.ContentId.make(address))),
          )).pipe(
            Effect.provide(
              Layer.provideMerge(layerCasAt(store, "sqlite"), layerDiskFs),
            ),
          )
        expect(verified.length).toBe(90)
      })
    ), 90_000)
})

/* ── 5. SIGKILL mid-put under load ───────────────────────────────── */

/** Boot the REAL daemon as a child process and read its banner off
 * stderr — the crash probe must kill an actual OS process, because a
 * fiber interrupt is an orderly death and the hazard is the disorderly
 * one. */
const spawnDaemon = (store: string): Effect.Effect<{
  readonly child: ReturnType<typeof Bun.spawn>
  readonly baseUrl: string
}, never, Scope.Scope> =>
  Effect.promise(async () => {
    const child = Bun.spawn(
      ["bun", casBin, "daemon", "--store", store, "--port", "0"],
      { stdin: "ignore", stdout: "ignore", stderr: "pipe" },
    )
    const reader = child.stderr.getReader()
    let buffered = ""
    const deadline = Date.now() + 20_000
    for (;;) {
      const dialable = buffered.match(/address=(http:\/\/[^\s]+)/u)?.[1]
      if (dialable !== undefined) {
        reader.releaseLock()
        return { child, baseUrl: dialable }
      }
      if (Date.now() > deadline) {
        throw new Error(`spawned daemon never bannered; stderr:\n${buffered}`)
      }
      const chunk = await reader.read()
      if (chunk.done) {
        throw new Error(`spawned daemon exited before bannering; stderr:\n${buffered}`)
      }
      buffered += decoder.decode(chunk.value)
    }
  }).pipe(
    // No leaked processes on ANY test outcome: a spawned daemon dies
    // with the probe's scope even when an assertion between spawn and
    // kill fails. Killing an already-exited process is a no-op.
    Effect.tap(({ child }) =>
      Effect.addFinalizer(() =>
        Effect.sync(() => {
          child.kill(9)
        }))),
  )

describe("daemon — SIGKILL mid-put under load (crash-matrix row 1)", () => {
  it.live("acknowledged admissions survive; the store reopens verified; a fresh daemon serves it", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const first = yield* spawnDaemon(store)

        // Concurrent puts against the real process; the kill lands
        // while many are in flight. An ack the client saw is a promise
        // the store must keep across the crash; a request that died
        // with the process is allowed to be lost (and is re-puttable
        // for free — that is what content addressing buys).
        const total = 160
        const acked: Array<string> = []
        const fire = Effect.forEach(
          Array.from({ length: total }, (_, index) =>
            encoder.encode(`crash-${index}`)),
          (payload) =>
            wirePut(first.baseUrl, payload).pipe(
              Effect.tap((ack) =>
                Effect.sync(() => {
                  if (ack.status === 201) acked.push(ack.address)
                })
              ),
              Effect.asVoid,
              Effect.catchCause(() => Effect.void),
            ),
          { concurrency: 24 },
        )
        const kill = Effect.promise(async () => {
          const deadline = Date.now() + 10_000
          while (acked.length < 40 && Date.now() < deadline) {
            await new Promise((resolve) => setTimeout(resolve, 5))
          }
          first.child.kill(9)
          await first.child.exited
        })
        yield* Effect.all([fire, kill], { concurrency: "unbounded" })

        expect(acked.length).toBeGreaterThanOrEqual(40)

        // Reopen the dirty store in-process: every acknowledged
        // address must load through the full read law — re-digested,
        // re-decoded, known kind.
        const verified = yield* Effect.forEach(acked, (address) =>
          Cas.Loader.pipe(
            Effect.flatMap((loader) => loader.load(Cas.ContentId.make(address))),
          )).pipe(
            Effect.provide(
              Layer.provideMerge(layerCasAt(store, "sqlite"), layerDiskFs),
            ),
          )
        expect(verified.length).toBe(acked.length)

        // And the daemon itself restarts on the crashed store: WAL
        // recovery is the driver's, serving again is ours.
        const second = yield* spawnDaemon(store)
        const caps = yield* Effect.promise(() =>
          fetch(`${second.baseUrl}/control/capabilities`, { headers: profileHeaders })
        )
        expect(caps.status).toBe(200)
        const sample = acked[0] ?? ""
        const reread = yield* Effect.promise(() =>
          fetch(`${second.baseUrl}/cas/${sample}`, { headers: profileHeaders })
        )
        expect(reread.status).toBe(200)
        second.child.kill()
        yield* Effect.promise(() => second.child.exited)
      })
    ), 120_000)
})

/* ── 5b. the front door ──────────────────────────────────────────── */

describe("daemon — the front door (Origin and Host, the MCP transport-security posture)", () => {
  it.live("a foreign Origin is refused on every plane; an allowed one gets CORS", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const handle = yield* bootDaemon({
          store,
          allowedOrigins: ["http://app.localhost:5173"],
        })

        // Foreign origin: refused before any plane sees it.
        const foreign = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/metrics`, {
            headers: { origin: "https://evil.example" },
          })
        )
        expect(foreign.status).toBe(403)
        const foreignWire = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/control/capabilities`, {
            headers: { ...profileHeaders, origin: "https://evil.example" },
          })
        )
        expect(foreignWire.status).toBe(403)

        // Allowed origin: answered, and the answer carries CORS.
        const allowed = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/projections`, {
            headers: { origin: "http://app.localhost:5173" },
          })
        )
        expect(allowed.status).toBe(200)
        expect(allowed.headers.get("access-control-allow-origin"))
          .toBe("http://app.localhost:5173")

        // The preflight is answered for the allowed origin.
        const preflight = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/mcp`, {
            method: "OPTIONS",
            headers: {
              origin: "http://app.localhost:5173",
              "access-control-request-method": "POST",
            },
          })
        )
        expect(preflight.status).toBe(204)
        expect(preflight.headers.get("access-control-allow-methods")).toContain("POST")

        // No-origin clients (every CLI, every launcher) are untouched.
        const plain = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/metrics`)
        )
        expect(plain.status).toBe(200)

        // A SAME-ORIGIN request — the daemon's own pages talking back
        // to it — passes without an allowlist entry (modern browsers
        // send Origin on same-origin POSTs too).
        const self = new URL(handle.baseUrl)
        const sameOrigin = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/metrics`, {
            headers: { origin: `http://${self.host}` },
          })
        )
        expect(sameOrigin.status).toBe(200)

        // The refusals were logged with their reason — the hoover
        // floor covers the security plane too.
        const refusedLines = handle.logsNow().filter((line) =>
          line.includes("refused=origin"))
        expect(refusedLines.length).toBeGreaterThanOrEqual(2)
      })
    ), 30_000)

  it.live("a foreign Host is refused — the DNS-rebinding posture", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const handle = yield* bootDaemon({ store })
        const rebound = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/metrics`, {
            headers: { host: "attacker.example" },
          })
        )
        expect(rebound.status).toBe(403)
        expect(handle.logsNow().some((line) => line.includes("refused=host"))).toBe(true)

        // The addresses this daemon actually answers on stay accepted.
        const loopback = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/metrics`)
        )
        expect(loopback.status).toBe(200)
      })
    ), 30_000)
})

  it.live("the two allowlists compare case-folded, in both directions", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        // Host names are ASCII case-insensitive on the wire. An
        // allowlist that compared them literally would 403 the
        // documented proxy deployment over a capitalization the
        // operator is entitled to write — in EITHER direction, since
        // either side may be the one carrying capitals.
        const allowlistCased = yield* bootDaemon({
          store,
          allowedHosts: ["Front.Example"],
        })
        for (const spelling of ["Front.Example", "front.example", "FRONT.EXAMPLE"]) {
          const answered = yield* Effect.promise(() =>
            fetch(`${allowlistCased.baseUrl}/metrics`, { headers: { host: spelling } })
          )
          expect(answered.status, `Host: ${spelling} against --allow-host Front.Example`)
            .toBe(200)
        }

        const allowlistFolded = yield* bootDaemon({
          store,
          allowedHosts: ["front.example"],
          allowedOrigins: ["http://App.Local:5173"],
        })
        const requestCased = yield* Effect.promise(() =>
          fetch(`${allowlistFolded.baseUrl}/metrics`, {
            headers: { host: "Front.Example" },
          })
        )
        expect(requestCased.status).toBe(200)

        // The origin allowlist folds the same way, and an allowed
        // origin still earns its CORS header in the spelling it sent.
        const originCased = yield* Effect.promise(() =>
          fetch(`${allowlistFolded.baseUrl}/projections`, {
            headers: { origin: "http://app.local:5173" },
          })
        )
        expect(originCased.status).toBe(200)
        expect(originCased.headers.get("access-control-allow-origin"))
          .toBe("http://app.local:5173")

        // A name that is not on either list is still refused: folding
        // widens spelling, never membership.
        const stranger = yield* Effect.promise(() =>
          fetch(`${allowlistFolded.baseUrl}/metrics`, {
            headers: { host: "Other.Example" },
          })
        )
        expect(stranger.status).toBe(403)
      })
    ), 30_000)

  it.live("an allowed Host does not admit a disallowed Origin — including on writes", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        // The transitive-trust defect: the same-origin allowance used
        // to compare the Origin against whatever Host had just been
        // allowed, so `--allow-host front.example` silently granted
        // `http://front.example` origin trust — and that origin WROTE
        // bytes into the store while the banner said every browser
        // Origin was refused. Host and Origin are independent gates.
        const handle = yield* bootDaemon({
          store,
          allowedHosts: ["front.example"],
          allowedOrigins: [],
        })
        const proxied = { host: "front.example", origin: "http://front.example" }

        for (const path of ["/metrics", "/projections", "/mcp"]) {
          const answered = yield* Effect.promise(() =>
            fetch(`${handle.baseUrl}${path}`, { headers: proxied })
          )
          expect(answered.status, `${path} under an allowed Host and an unlisted Origin`)
            .toBe(403)
        }

        // The write plane, where the audit found bytes landing.
        const payload = encoder.encode("origin-must-not-write")
        const { address, bytes } = yield* nodeOf(payload)
        const refused = yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/cas/${address}`, {
            method: "PUT",
            headers: { ...octetHeaders, ...proxied },
            body: bytes.slice(),
          })
        )
        expect(refused.status).toBe(403)

        // ...and nothing landed. A first admission answers 201 and a
        // repeat answers 200, so a 201 here is the store saying it had
        // never seen these bytes.
        const admitted = yield* wirePut(handle.baseUrl, payload)
        expect(admitted.status).toBe(201)

        // The banner states the ENFORCED posture, not the intended one.
        const banner = handle.logsNow().find((line) =>
          line.includes("message=\"daemon serving\"")
        )
        expect(banner).toContain("none configured")
        expect(banner).not.toContain("every browser Origin refused")
      })
    ), 30_000)

  it.live("a refusal names the defect and the fix, in each plane's own media type", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const handle = yield* bootDaemon({ store })
        const foreign = { origin: "https://evil.example" }

        // The metrics plane answers in Prometheus' comment syntax, so
        // a scraper's own eyes can read the refusal.
        const metrics = yield* Effect.promise(async () => {
          const response = await fetch(`${handle.baseUrl}/metrics`, { headers: foreign })
          return {
            status: response.status,
            type: response.headers.get("content-type"),
            body: await response.text(),
          }
        })
        expect(metrics.status).toBe(403)
        expect(metrics.type).toContain("text/plain")
        expect(metrics.body).toContain("# refused:")
        expect(metrics.body).toContain("--allow-origin")

        // The JSON planes answer in JSON, with the fix as a field.
        for (const path of ["/projections", "/mcp"]) {
          const answered = yield* Effect.promise(async () => {
            const response = await fetch(`${handle.baseUrl}${path}`, { headers: foreign })
            return {
              status: response.status,
              type: response.headers.get("content-type"),
              body: await response.json() as { readonly fix?: string },
            }
          })
          expect(answered.status).toBe(403)
          expect(answered.type).toContain("application/json")
          expect(answered.body.fix).toContain("--allow-origin")
        }

        // The Host refusal names the OTHER flag, because it is a
        // different defect with a different repair.
        const rebound = yield* Effect.promise(async () => {
          const response = await fetch(`${handle.baseUrl}/projections`, {
            headers: { host: "attacker.example" },
          })
          return await response.json() as { readonly fix?: string }
        })
        expect(rebound.fix).toContain("--allow-host")

        // cas-http/0 stays OCTET-BARE: the profile's framing rules a
        // JSON body out, so the status is the whole sentence there.
        const wire = yield* Effect.promise(async () => {
          const response = await fetch(`${handle.baseUrl}/control/capabilities`, {
            headers: { ...profileHeaders, ...foreign },
          })
          return { status: response.status, body: await response.text() }
        })
        expect(wire.status).toBe(403)
        expect(wire.body).toBe("")
      })
    ), 30_000)

  it.live("the request timer publishes finite buckets — no le=\"Infinity\" row", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const handle = yield* bootDaemon({ store })
        yield* Effect.promise(() =>
          fetch(`${handle.baseUrl}/control/capabilities`, { headers: profileHeaders })
        )
        const exposition = yield* Effect.promise(async () => {
          const response = await fetch(`${handle.baseUrl}/metrics`)
          return await response.text()
        })
        expect(exposition).toContain("cas_daemon_request_bucket")
        // The default timer boundaries end in Infinity, which the
        // exporter renders as a bucket AND then follows with its own
        // +Inf row. Finite boundaries leave exactly one overflow row.
        expect(exposition).not.toContain('le="Infinity"')
        expect(exposition).toContain('le="+Inf"')
      })
    ), 30_000)

/* ── 5c. projections ─────────────────────────────────────────────── */

describe("daemon — projections (tier 0 of the front end)", () => {
  it.live("serves the emitted artifacts read-only, with an index", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const handle = yield* bootDaemon({ store })

        const index = yield* Effect.promise(async () => {
          const response = await fetch(`${handle.baseUrl}/projections`)
          return {
            status: response.status,
            body: await response.json() as {
              readonly projections: ReadonlyArray<{
                readonly name: string
                readonly present: boolean
              }>
            },
          }
        })
        expect(index.status).toBe(200)
        const manifestRow = index.body.projections.find((row) =>
          row.name === "cas-tools.json")
        expect(manifestRow?.present).toBe(true)

        // The manifest projection IS the emitted document the boot
        // gate checked — served, never authored.
        const manifest = yield* Effect.promise(async () => {
          const response = await fetch(`${handle.baseUrl}/projections/cas-tools.json`)
          return {
            status: response.status,
            contentType: response.headers.get("content-type"),
            body: await response.json() as {
              readonly language?: string
              readonly tools?: ReadonlyArray<{ readonly name: string }>
            },
          }
        })
        expect(manifest.status).toBe(200)
        expect(manifest.contentType).toContain("application/json")
        expect(manifest.body.language).toBe("cas")
        expect(manifest.body.tools?.map((tool) => tool.name)).toContain("cas_put")
      })
    ), 30_000)
})

/* ── 5d. graceful shutdown ───────────────────────────────────────── */

describe("daemon — SIGTERM is a drain, not a drop", () => {
  it.live("the process exits promptly and cleanly on SIGTERM", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        const running = yield* spawnDaemon(store)
        // Alive and serving...
        const caps = yield* Effect.promise(() =>
          fetch(`${running.baseUrl}/control/capabilities`, { headers: profileHeaders })
        )
        expect(caps.status).toBe(200)
        // ...then asked to stop: the server layer's finalizer performs
        // Bun's graceful stop (drain, then force-close at the
        // deadline), and the runtime exits without a crash.
        const exitCode = yield* Effect.promise(async () => {
          running.child.kill("SIGTERM")
          return await running.child.exited
        }).pipe(Effect.timeoutOrElse({
          duration: Duration.seconds(10),
          orElse: () => Effect.sync(() => {
            running.child.kill(9)
            return -1
          }),
        }))
        // 130 is the runtime's documented interruption-only exit
        // (`Runtime.ts:77-113` at the pin): the signal was HANDLED —
        // main fiber interrupted, finalizers (including the server
        // layer's graceful stop) run — and then the process exited. A
        // raw unhandled SIGTERM would be 143, and a crash would be 1.
        expect(exitCode).toBe(130)
      })
    ), 30_000)
})

/* ── 6. refuse-first ─────────────────────────────────────────────── */

describe("daemon — a credentialed policy refuses the boot", () => {
  it.effect("anonymousReads: false is a typed refusal, never open service", () =>
    Effect.gen(function* () {
      const gated: ServePolicy = {
        ...defaultServePolicy,
        anonymousReads: false,
        credentialEnv: "CAS_CREDENTIAL",
      }
      const exit = yield* Effect.exit(applyDaemonPolicy({
        policy: gated,
        host: "127.0.0.1",
        port: Option.none(),
        otlp: Option.none(),
        replicaTarget: Option.none(),
      }))
      expect(exit._tag).toBe("Failure")
      const rendered = JSON.stringify(exit)
      expect(rendered).toContain("daemon/CredentialedPolicyUndaemonable")
      expect(rendered).toContain("CAS_CREDENTIAL")
    }))

  it.effect("the config schema still admits the gated policy — the refusal is the daemon's, not the decoder's", () =>
    Effect.gen(function* () {
      // A store may legitimately carry a gated policy for a future
      // credentialed host; decoding must not lose it.
      const decoded = StoreConfig.make({
        backend: "sqlite",
        serve: { ...defaultServePolicy, anonymousReads: false },
      })
      expect(decoded.serve?.anonymousReads).toBe(false)
    }))
})

/* ── 6b. an unreadable config is not an absent one ───────────────── */

/** One CLI invocation run to completion: its exit code and what it
 * said. Used where the assertion IS the refusal — a boot that must not
 * happen cannot be probed over HTTP. */
const runCas = (
  argv: ReadonlyArray<string>,
): Effect.Effect<{ readonly exitCode: number; readonly stderr: string }> =>
  Effect.promise(async () => {
    const child = Bun.spawn(["bun", casBin, ...argv], {
      stdin: "ignore",
      stdout: "ignore",
      stderr: "pipe",
    })
    // A host that WRONGLY booted would never exit; the kill turns that
    // into a failed assertion instead of a hung suite.
    const guard = setTimeout(() => child.kill(9), 20_000)
    const [exitCode, stderr] = await Promise.all([
      child.exited,
      new Response(child.stderr).text(),
    ])
    clearTimeout(guard)
    return { exitCode, stderr }
  })

describe("both hosts — a config that will not read refuses the boot", () => {
  it.live("an unreadable config.json is a refusal, never the open defaults", () =>
    Effect.scoped(Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const root = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-badconfig-" })

      // The defaults a missing config falls back to include
      // `anonymousReads: true`. So a reader that answered "absent" to
      // a file it could not OPEN would serve a store whose config says
      // `anonymousReads: false` wide open, on both hosts, on the
      // strength of a permission bit — the gate inverted by the
      // failure to read it. Both backends, because they reach the
      // config by different paths.
      for (const backend of ["sqlite", "file"] as const) {
        const store = `${root}/${backend}`
        yield* fs.makeDirectory(store, { recursive: true })
        yield* initStore(store, true, backend).pipe(Effect.orDie)

        // A directory where the file belongs is unreadable on every
        // platform this package runs on, chmod or no chmod.
        yield* fs.remove(`${store}/config.json`)
        yield* fs.makeDirectory(`${store}/config.json`)

        for (const verb of ["daemon", "serve"] as const) {
          const argv = verb === "daemon"
            ? ["daemon", "--store", store, "--port", "0"]
            : ["serve", "--store", store]
          const ran = yield* runCas(argv)
          expect(ran.exitCode, `cas ${verb} on a ${backend} store with an unreadable config`)
            .not.toBe(0)
          // Grade A: the defect named, the fix named — and the store
          // still FOUND, because an unreadable config decides only that
          // the layout is unknown, never that there is no store here.
          expect(ran.stderr).toContain("the store's config will not read")
          expect(ran.stderr).toContain("check its permissions")
          expect(ran.stderr).not.toContain("no store at")
        }
      }
    })).pipe(Effect.provide(Layer.merge(layerDiskFs, Path.layer))), 60_000)

  it.effect("the reader itself keeps absent and unreadable apart", () =>
    Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const root = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-configread-" })
      const store = `${root}/store`
      yield* initStore(store, true, "file").pipe(Effect.orDie)
      const location = yield* locateStore(Option.some(store)).pipe(Effect.orDie)

      // Present and decodable.
      expect(Option.isSome(yield* readConfig(location))).toBe(true)

      // Absent: the one case that may default.
      yield* fs.remove(location.configPath)
      expect(Option.isNone(yield* readConfig(location))).toBe(true)

      // Present and unreadable: a typed refusal, not an absence.
      yield* fs.makeDirectory(location.configPath)
      const exit = yield* Effect.exit(readConfig(location))
      expect(exit._tag).toBe("Failure")
      expect(JSON.stringify(exit)).toContain("cli/ConfigUnreadable")
    }).pipe(
      Effect.scoped,
      Effect.provide(Layer.merge(layerDiskFs, Path.layer)),
    ))
})

/* ── 6c. a bind that cannot happen ───────────────────────────────── */

describe("daemon — a bind that cannot happen is a refusal, not a stack dump", () => {
  it.live("names the condition and the fix in one line, through the typed channel", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        // Somebody else's port. `BunHttpServer.layer` DIES when
        // `Bun.serve` throws, and a defect routes around every
        // `Effect.mapError` between the layer and the CLI — which is
        // how a failed bind became a stack trace carrying the
        // platform's own wrong sentence ("Is port 0 in use?" for a
        // --host this machine does not hold).
        const squatter = yield* Effect.acquireRelease(
          Effect.sync(() =>
            Bun.serve({ port: 0, hostname: "127.0.0.1", fetch: () => new Response("held") })
          ),
          (server) => Effect.sync(() => void server.stop(true)),
        )
        const taken = squatter.port ?? 0
        expect(taken).toBeGreaterThan(0)
        const exit = yield* Effect.exit(Effect.scoped(Layer.build(
          layerDaemon({
            policy: defaultServePolicy,
            host: "127.0.0.1",
            port: Option.some(taken),
            otlp: Option.none(),
            replicaTarget: Option.none(),
          }).pipe(
            Layer.provideMerge(layerCasAt(store, "sqlite")),
            Layer.provideMerge(Layer.merge(layerDiskFs, Path.layer)),
          ),
        )))
        expect(exit._tag).toBe("Failure")
        const rendered = JSON.stringify(exit)
        expect(rendered).toContain("daemon/BindRefused")
        expect(rendered).toContain("already holds")
        expect(rendered).toContain("--port 0")
      })
    ), 30_000)

  it.live("a privileged port is diagnosed as privileged, not as busy", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        // The pinned Bun answers all three bind failures with the SAME
        // code and a message that names the wrong port on two of the
        // three, so the diagnosis is derived from the address that was
        // ASKED for. Port 80 under a non-root process is the case that
        // derivation gets right and the platform gets wrong.
        const exit = yield* Effect.exit(Effect.scoped(Layer.build(
          layerDaemon({
            policy: { ...defaultServePolicy, port: 80 },
            host: "127.0.0.1",
            port: Option.none(),
            otlp: Option.none(),
            replicaTarget: Option.none(),
          }).pipe(
            Layer.provideMerge(layerCasAt(store, "sqlite")),
            Layer.provideMerge(Layer.merge(layerDiskFs, Path.layer)),
          ),
        )))
        expect(exit._tag).toBe("Failure")
        const rendered = JSON.stringify(exit)
        expect(rendered).toContain("daemon/BindRefused")
        expect(rendered).toContain("privileged")
      })
    ), 30_000)
})

/* ── 6d. a failing export is audible ─────────────────────────────── */

describe("daemon — an OTLP export that is not landing says so", () => {
  it.live("warns on the first failure instead of exporting into silence", () =>
    withSqliteStore((store) =>
      Effect.gen(function* () {
        // A collector that is not there. The upstream exporter answers
        // this by disabling itself for 60 s and logging that at DEBUG,
        // which an Info-and-above stderr logger drops — so `--otlp`
        // against a dead collector used to look exactly like `--otlp`
        // against a live one.
        const dead = yield* Effect.sync(() => {
          const probe = Bun.serve({ port: 0, hostname: "127.0.0.1", fetch: () => new Response("") })
          const port = probe.port ?? 0
          probe.stop(true)
          return port
        })
        expect(dead).toBeGreaterThan(0)

        const handle = yield* bootDaemon({
          store,
          otlp: `http://127.0.0.1:${dead}`,
        })
        // The three exporters export on their own intervals (1 s, 5 s,
        // 10 s at the pin) and each retries transiently before giving
        // up, so the first failure is SEVERAL seconds out and its
        // exact timing is not this probe's business. Polled, not
        // slept-on.
        const saidIt = (): ReadonlyArray<string> =>
          handle.logsNow().filter((line) => line.includes("message=\"otlp export failing\""))
        yield* Effect.promise(async () => {
          const deadline = Date.now() + 25_000
          while (saidIt().length === 0 && Date.now() < deadline) {
            await new Promise((resolve) => setTimeout(resolve, 200))
          }
        })

        const warnings = saidIt()
        expect(warnings.length).toBeGreaterThanOrEqual(1)
        expect(warnings[0]).toContain(`http://127.0.0.1:${dead}`)
        // Rate-limited: an outage is one line a minute, not a flood.
        expect(warnings.length).toBeLessThanOrEqual(2)

        // And the pull surface is untouched by the push being down.
        const metrics = yield* Effect.promise(() => fetch(`${handle.baseUrl}/metrics`))
        expect(metrics.status).toBe(200)
      })
    ), 40_000)
})

/* ── 7. replica lag ──────────────────────────────────────────────── */

describe("daemon — replica lag is measured, or says why not", () => {
  it.live("no configured target: the gauge says -1 and the log says why", () =>
    Effect.gen(function* () {
      const logs: Array<string> = []
      const layerCapture = Logger.layer([
        Logger.map(Logger.formatLogFmt, (line: string) => {
          logs.push(line)
        }),
      ])
      // Read from the process-wide default registry: a metric's first
      // touch pins its registry hook on the metric object itself
      // (`Metric.ts:1686-1693` at the pin), so a fresh per-test map
      // would be silently ignored after any earlier test touched the
      // gauge. Tests in this file run sequentially, so the last write
      // is the one under assertion.
      yield* Effect.scoped(
        Layer.build(layerReplicaLag(Option.none()).pipe(
          Layer.provide(layerCapture),
          Layer.provide(Layer.merge(layerDiskFs, Path.layer)),
        )).pipe(Effect.andThen(
          Metric.snapshot.pipe(Effect.flatMap((snapshots) =>
            Effect.sync(() => {
              const gauge = snapshots.find((snapshot) =>
                snapshot.id === "cas.replica.age_ms")
              expect(gauge?.type).toBe("Gauge")
              expect(
                gauge?.type === "Gauge" ? gauge.state.value : undefined,
              ).toBe(-1)
            })
          )),
        )),
      )
      expect(logs.some((line) =>
        line.includes("replica lag unmeasured")
        && line.includes("backup.target"))).toBe(true)
    }))

  it.live("a named local replica directory is measured as now minus its newest write", () =>
    Effect.scoped(Effect.gen(function* () {
      const fs = yield* FileSystem.FileSystem
      const replica = yield* fs.makeTempDirectoryScoped({ prefix: "foldlab-replica-" })
      yield* fs.makeDirectory(`${replica}/generations/abc/wal`, { recursive: true })
      yield* fs.writeFile(
        `${replica}/generations/abc/wal/00000001.wal.lz4`,
        encoder.encode("segment"),
      )
      yield* Effect.scoped(
        Layer.build(layerReplicaLag(Option.some(replica)).pipe(
          Layer.provide(Layer.merge(layerDiskFs, Path.layer)),
        )).pipe(Effect.andThen(
          // The sampler's first pass runs at fork; give it a beat.
          Effect.sleep(Duration.millis(300)).pipe(Effect.andThen(
            Metric.snapshot.pipe(Effect.flatMap((snapshots) =>
              Effect.sync(() => {
                const gauge = snapshots.find((snapshot) =>
                  snapshot.id === "cas.replica.age_ms")
                const value = gauge?.type === "Gauge" ? gauge.state.value : undefined
                expect(value).toBeDefined()
                // Freshly written: the age is real and small.
                expect(value).toBeGreaterThanOrEqual(0)
                expect(value).toBeLessThan(60_000)
              })
            )),
          )),
        )),
      )
    })).pipe(Effect.provide(Layer.merge(layerDiskFs, Path.layer))))
})
