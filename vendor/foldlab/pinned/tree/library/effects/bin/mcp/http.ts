/**
 * The daemon host — both planes on one port.
 *
 * `cas daemon` is the long-lived sibling of `cas serve`: one Bun HTTP
 * server binding the two wire surfaces the estate already ratified,
 * over the SAME store composition and under the SAME boot-time
 * manifest gate as the stdio host. Nothing semantic is minted here —
 * this file is the bind the audit priced at ~50 lines, plus the
 * production discipline around it.
 *
 * ## The two planes, one port
 *
 * - **cas-http/0** — the profile's three resource spaces (`/cas/{hex}`,
 *   `/roots/{hex}`, `/control/…`), served by the existing transport-free
 *   core (`src/server/Core.ts` under `src/server/HttpApp.ts`) through a
 *   wildcard route. This is that core's first bind ever. The wire law
 *   answers EVERY UNCLAIMED EXCHANGE — an unknown path or wrong method
 *   is the PROFILE's refusal (400/405 from the status table), not a
 *   router 404, because the wildcard hands each of them to `decide`.
 *   Not every exchange on the port: four co-tenant prefixes are
 *   claimed before the wildcard sees them, and the profile's own §14
 *   enumerates them as outside its media-type and status law.
 * - **MCP over HTTP** — `McpServer.layerHttp` at `/mcp`: the
 *   single-endpoint Streamable HTTP topology at the pin (no legacy
 *   two-endpoint SSE, no event resumption, no session expiry — the
 *   adapter's own documented scope). The tool table is the SAME
 *   `casToolkit` the stdio host serves, behind the SAME
 *   `layerHandlers` gate, after the SAME manifest agreement check —
 *   the gate is transport-independent law.
 *
 * Three more routes share the port and are host surface, not protocol:
 * `/metrics` (Prometheus exposition, decision 20's first production
 * sensor), `/projections` (below), and `/history` — the store's own
 * word, read-only, paged by mark and bound, the feed the front end
 * polls. They are the profile's declared CO-TENANTS
 * (PROFILE-CAS-HTTP-0 §14); everything unclaimed falls to the profile.
 *
 * ## The `ServePolicy`, honored for real this time
 *
 * The stdio host ruled each field explicitly and refused what stdio
 * cannot honor. The daemon is the transport most of those numbers were
 * written for:
 *
 * - `port` — HONORED. The bind address; a `--port` flag overrides for
 *   one invocation without rewriting the store's config.
 * - `maxNodeBytes` — HONORED on BOTH planes, and CLAMPED under the
 *   transport frame cap exactly as stdio clamps it. On the MCP plane a
 *   payload crosses as hex inside a JSON body, so `2 × maxNodeBytes +
 *   slack` must stay under the body cap for the host's own
 *   `mcp/NodeTooLarge` to fire first; the cas-http/0 plane carries raw
 *   octets and the same effective number becomes the capability
 *   document's published bound, so the two planes publish ONE cap.
 * - `maxInFlight` — HONORED, PER PLANE. The MCP plane's bound is the
 *   semaphore inside `layerHandlers` (BS-1); the cas-http/0 plane gets
 *   its own semaphore of the same size here. The store can therefore
 *   see at most `2 × maxInFlight` store-touching calls when both
 *   planes saturate — said out loud at startup rather than hidden,
 *   because one shared gate would mean reaching into the handler
 *   layer's internals, and that layer is another lane's file.
 * - `maxBatchKeys` — HONORED on the cas-http/0 plane (the
 *   `/control/missing` batch bound the field was written for). Still
 *   not applicable to MCP, exactly as on stdio.
 * - `anonymousReads: false` — REFUSED AT BOOT, exactly as stdio
 *   refuses it (the refuse-first ruling). The protocol layer under
 *   `src/server/Protocol.ts` can check a bearer credential, but a
 *   credentialed HTTP story is a named NON-GOAL of `cas daemon` v0:
 *   serving it would put a secret on a wire this host has no TLS for —
 *   TLS is the adopted front proxy's job (see library/effects/SERVING.md)
 *   — so a store that gates reads is not served until the credentialed
 *   story lands as its own ruled slice.
 *
 * ## The frame cap
 *
 * On stdio the transport's 16 MiB NDJSON cap LOSES an oversized
 * request (the audit's sharpest finding). On HTTP the equivalent cap
 * is Bun's `maxRequestBodySize`, which this host pins to the SAME
 * number — and Bun REFUSES an oversized body with an HTTP error
 * instead of dropping it, so on this transport even the over-cap case
 * is an answer, never silence. The clamp keeps the host's own typed
 * refusals (`mcp/NodeTooLarge`, the profile's 413) firing before the
 * transport's for every payload the policy admits.
 *
 * ## Vital signs
 *
 * The stdio heartbeat discipline extends unchanged: `layerHeartbeat`
 * beats every 2 s carrying the metric snapshot, and a missing beat IS
 * a detected stall. The daemon adds three sensors of its own —
 * `cas.daemon.request` (request duration, attributed by plane),
 * `cas.daemon.inflight` (the wire plane's own gauge, beside the MCP
 * plane's `cas.host.inflight`), and `cas.replica.age_ms` (how far the
 * litestream replica is behind, where the config names a local one;
 * `-1` when unmeasured, and the log says why). All of it is scraped at
 * `/metrics`, and `--otlp <baseUrl>` exports logs, metrics, and spans
 * as OTLP/JSON besides.
 *
 * ## Logs
 *
 * logfmt on stderr, same as stdio. Every request is answered by one
 * `request` line — seq, plane, method, path, status, ms — where `seq`
 * is a per-boot monotone counter, so a reader can reconstruct event
 * order even when two lines share a millisecond. The MCP handlers'
 * own per-tool lines (tool, address, outcome) arrive between them,
 * exactly as they do on stdio. The field vocabulary is documented in
 * library/effects/SERVING.md; it is the first sensor of decision 20's
 * logging hoover, so the fields are STABLE — a rename is a versioning
 * event for whatever learns to read them.
 *
 * ## The front door (MCP security guidance, applied to the whole port)
 *
 * The MCP spec's transport security guidance names the local-daemon
 * attack precisely: a malicious web page scripting requests at a
 * localhost server, either cross-origin or through DNS rebinding. The
 * pin's own MCP endpoint already refuses any browser `Origin` it was
 * not told to allow; this host extends that exact posture to EVERY
 * route on the port, plus the Host-header check the rebinding attack
 * requires:
 *
 * - A request whose `Host` does not name a loopback host, the bound
 *   host, or a `--allow-host` entry is refused 403 — a DNS-rebinding
 *   request arrives at 127.0.0.1 carrying the attacker's own Host.
 * - A request carrying an `Origin` outside `--allow-origin` is refused
 *   403 on every plane. No origins are allowed by default; non-browser
 *   clients send no Origin and are unaffected. The ONE Origin that
 *   passes without an entry is this daemon's own — a page it served
 *   itself, recognized by a Host that is loopback or the bound
 *   address.
 * - The two gates are INDEPENDENT. `--allow-host` widens which Host
 *   names are answered and nothing else; it never grants origin
 *   trust. It used to, transitively: the same-origin allowance
 *   compared the Origin against whatever Host had just been allowed,
 *   so under `--allow-host` an unlisted browser origin passed every
 *   plane and WROTE bytes into the store while the banner said every
 *   browser Origin was refused. Origin is enforced from
 *   `--allow-origin` plus this daemon's own addresses, full stop.
 * - Both allowlists compare CASE-FOLDED, on insert and on compare.
 *   Host names and origins are ASCII case-insensitive on the wire, so
 *   a literal comparison 403s the documented proxy deployment over a
 *   capitalization the operator is entitled to write.
 * - An allowed origin gets real CORS: the preflight is answered and
 *   the response carries `access-control-allow-origin`, which is what
 *   lets the browser front end read this host's projections.
 * - A refusal answers with a BODY that names the defect and the fix,
 *   in the media type of the plane that answered — except on
 *   cas-http/0, where the profile's framing rules the body out and
 *   the status is the whole sentence (see `refusedResponse`).
 *
 * ## Projections — tier 0 of the front end
 *
 * The emitted, byte-gated JSON artifacts are served read-only under
 * `/projections/…` (index at `/projections`): the tool manifest, the
 * surface and obligations ledgers, the schema index, the environment
 * ledger. The daemon SERVES these files and never authors them — they
 * are the Lean emitters' output, read from disk per request so a
 * regenerate is visible without a restart.
 *
 * This plane is RULED, not assumed: decision 32(a) released tier-0
 * serving to the daemon ("`/projections` RELEASED to the daemon —
 * tier-0 serving of the emitted, byte-gated artifacts is the
 * daemon's, read-only"), replacing FRONTEND.md's earlier static-host
 * story. Read-only is the whole of the mandate: there is no write
 * verb on this plane and no authorship in this file.
 *
 * ## Shutdown
 *
 * SIGINT/SIGTERM interrupt the runtime, and the server layer's
 * finalizer performs Bun's graceful stop: stop accepting, drain
 * in-flight requests, then force-close at the timeout. In-flight MCP
 * calls that do not finish in time are LOST WITHOUT NOTICE to the
 * client — the same in-flight-loss semantics as a crash — and the
 * store-side recovery is the same: puts are idempotent, re-put is
 * free (SERVING.md states this on the wire surface).
 */
import { BunHttpServer } from "@effect/platform-bun"
import {
  Cause,
  Clock,
  Duration,
  Effect,
  Exit,
  FileSystem,
  Layer,
  Metric,
  Option,
  Path,
  Schema,
  Semaphore,
} from "effect"
import { McpServer } from "effect/unstable/ai"
import {
  FetchHttpClient,
  HttpClient,
  HttpRouter,
  HttpServer,
  HttpServerRequest,
  HttpServerResponse,
} from "effect/unstable/http"
import { Otlp, PrometheusMetrics } from "effect/unstable/observability"
import { Cas, Server } from "../../src/index.ts"
import { canonicalJson } from "../../src/cas/Value.ts"
import { wordHistorySchema } from "../../src/cas/generated/WordLogSchema.ts"
import type { ServePolicy } from "../cli/store.ts"
import { layerHandlers } from "./handlers.ts"
import {
  frameSlackBytes,
  gateOnManifest,
  type HostLimits,
  maxServableNodeBytes,
  offeredProtocols,
  serverIdentity,
  transportFrameBytes,
} from "./server.ts"
import { heartbeatInterval, layerHeartbeat } from "./telemetry.ts"
import { casToolkit } from "./tools.ts"

/* ── the port's address space ────────────────────────────────────── */

/** Where MCP-over-HTTP answers. One POST endpoint, per the pin's
 * Streamable HTTP adapter; other methods on it answer 405. */
export const mcpPath = "/mcp"

/** Where Prometheus scrapes. */
export const metricsPath = "/metrics"

/** Where the emitted JSON artifacts are served read-only — tier 0 of
 * the front end. */
export const projectionsPath = "/projections"

/** Where the store's own word is read — the history feed the front end
 * polls. One exported constant, so the router, `planeOf`, the banner,
 * and the drift gate all name the same string and none of them
 * hand-types it. */
export const historyPath = "/history"

/** The one cas-http/0 read served outside the admission gate — it
 * touches no store, and a saturated store must not make the host look
 * dead to a client asking what it serves (the same ruling that keeps
 * `tools/list` outside the stdio gate). */
const capabilitiesPath = "/control/capabilities"

/** Which plane answered a path — the attribute every request metric
 * and request log line carries, and the media type every REFUSAL wears
 * (`refusedResponse` branches on it). A route missing from this
 * function is not merely mislabelled in the log: its refusals go out
 * as cas-http/0's, which is octet-bare with no body at all, so the
 * operator sees a naked status and the client sees nothing. */
const planeOf = (path: string): string =>
  path === mcpPath
    ? "mcp"
    : path === metricsPath
    ? "metrics"
    : path === projectionsPath || path.startsWith(`${projectionsPath}/`)
    ? "projections"
    : path === historyPath
    ? "history"
    : "cas-http/0"

/* ── the daemon's own sensors ────────────────────────────────────── */

/** Bucket boundaries for request latency, in milliseconds, and FINITE
 * on purpose.
 *
 * `Metric.timer`'s default boundaries END in `Infinity`
 * (`Metric.ts:2786-2788` over `boundariesFromIterable`, which appends
 * it), and the Prometheus exposition renders every boundary as a
 * bucket with `le=boundary.toString()` and THEN appends its own
 * `le="+Inf"` row (`PrometheusMetrics.ts:419-427`). The default
 * therefore publishes a duplicate overflow bucket labelled
 * `le="Infinity"`, which is not a number Prometheus parses. Finite
 * boundaries end it: an observation past the top lands in the
 * histogram's own overflow slot, which the exporter reports as
 * `+Inf`, exactly where a scraper looks for it.
 *
 * The set spans what a request to this daemon actually costs — a
 * loopback capability read at the bottom, a stalled one at the top. */
export const requestDurationBoundaries: ReadonlyArray<number> = [
  1,
  2,
  5,
  10,
  25,
  50,
  100,
  250,
  500,
  1000,
  2500,
  5000,
  10000,
]

/** Request duration, attributed by plane — the daemon's first number
 * beyond BS-1's four. */
export const requestDuration = Metric.timer("cas.daemon.request", {
  description: "HTTP request duration, by plane",
  boundaries: requestDurationBoundaries,
})

/** The wire plane's in-flight gauge, beside the MCP plane's
 * `cas.host.inflight` — two planes, two gates, two gauges, so a reader
 * can tell which surface is saturated. */
export const wireInflight = Metric.gauge("cas.daemon.inflight", {
  description: "cas-http/0 requests currently past the admission gate",
})

/** How stale the litestream replica is, in milliseconds — the audit's
 * "lag unbounded and unmeasured" gap, measured. `-1` means unmeasured,
 * and the startup log names why: no `backup.target` in the config, or
 * a non-local target this host cannot stat (scrape litestream's own
 * metrics endpoint for those). */
export const replicaAge = Metric.gauge("cas.replica.age_ms", {
  description:
    "milliseconds since the litestream replica last advanced; -1 when unmeasured",
})

/** Resident memory. The honest sensor for the two unbounded growths a
 * long-lived host cannot bound from inside: the transport's outbound
 * queues, and the pin's MCP-over-HTTP session map, which is only ever
 * added to (`McpServer.ts:2314` sets; nothing deletes — no session
 * expiry at this pin, per the adapter's own docs). Watch this gauge;
 * its slope under steady traffic is those leaks' measurement. */
export const rssBytes = Metric.gauge("cas.daemon.rss_bytes", {
  description: "resident set size of the daemon process",
})

/* ── policy, ruled for the daemon ────────────────────────────────── */

/** A store whose policy gates reads has no daemon spelling YET — the
 * credentialed HTTP story is a named non-goal of v0, refused at boot
 * per the refuse-first ruling rather than served open. */
export class CredentialedPolicyUndaemonable
  extends Schema.TaggedError<CredentialedPolicyUndaemonable>()(
    "daemon/CredentialedPolicyUndaemonable",
    { credentialEnv: Schema.optionalKey(Schema.String) },
  )
{
  override get message(): string {
    return [
      "this store's serve policy requires a credential for reads, and cas daemon does not speak credentials yet",
      this.credentialEnv === undefined
        ? "  config.json says anonymousReads: false"
        : `  config.json says anonymousReads: false, credentialEnv: ${this.credentialEnv}`,
      "  credentialed HTTP is a named non-goal of daemon v0 — this host has no TLS of its own, and a bearer credential belongs behind the front proxy's TLS",
      "  set anonymousReads: true to serve this store open, or wait for the credentialed slice",
    ].join("\n")
  }
}

/**
 * A bind that did not happen, said in one line.
 *
 * `BunHttpServer.layer` DIES rather than fails when `Bun.serve`
 * throws, and a defect routes around every `Effect.mapError` between
 * here and the CLI — so the landed behavior was a stack trace
 * carrying the platform's own wrong sentence. This is the typed
 * refusal that replaces it: one logfmt-compatible line, the condition
 * named, the fix named.
 */
export class DaemonBindRefused extends Schema.TaggedError<DaemonBindRefused>()(
  "daemon/BindRefused",
  {
    host: Schema.String,
    port: Schema.Int,
    condition: Schema.String,
    fix: Schema.String,
    /** What the platform said, kept for a debugger and deliberately
     * NOT quoted in the message — at this pin it misdiagnoses (see
     * `bindDiagnosis`). */
    platformSaid: Schema.String,
  },
) {
  override get message(): string {
    return `the daemon did not bind ${this.host}:${this.port} — ${this.condition}; ${this.fix}`
  }
}

/**
 * What a failed bind actually was, derived from what this host KNOWS.
 *
 * The platform is not a witness here. Measured at the pinned Bun: a
 * port already in use, a `--host` this machine does not hold, and a
 * privileged port all throw the SAME `code: "EADDRINUSE"`, and two of
 * the three name the wrong port in the message (`Bun.serve({ port: 0,
 * hostname: "203.0.113.77" })` says "Is port 0 in use?"). Reading the
 * diagnosis off that error would be repeating a guess. So the
 * condition is derived from the address that was ASKED for, and where
 * two causes remain indistinguishable both are named with the way to
 * tell them apart.
 */
const bindDiagnosis = (
  host: string,
  port: number,
): { readonly condition: string; readonly fix: string } =>
  port !== 0 && port < 1024
    ? {
      condition:
        `port ${port} is privileged (below 1024) and this process does not have the right to bind it`,
      fix:
        "use a port above 1024 — 80 and 443 belong to the front proxy, which is what terminates TLS for this daemon",
    }
    : loopbackHosts.includes(hostName(host)) || host === "0.0.0.0" || host === "::"
    ? {
      condition: `something else already holds ${host}:${port}`,
      fix:
        `stop whatever holds it, pass --port <other>, or pass --port 0 to let the OS choose a free one`,
    }
    : {
      condition:
        `${host}:${port} could not be taken — either --host names an address this machine does not hold, or something else already holds that port`,
      fix:
        "check --host against this machine's own addresses first, then the port; --port 0 lets the OS choose one",
    }

/** A build failure's text, flattened to one logfmt-safe line. */
const causeLine = (cause: Cause.Cause<never>): string =>
  Cause.prettyErrors(cause)
    .map((pretty) => pretty.message)
    .join("; ")
    .replaceAll(/\s+/gu, " ")
    .slice(0, 200)

/**
 * A layer whose BUILD failure becomes a typed refusal rather than a
 * defect. `Layer.catchCause`'s fallback must produce the same
 * services, and a server that did not bind has none to give — so the
 * fallback is `Layer.unwrap` over a failing effect, which keeps the
 * output services in the type while replacing the error channel.
 */
const refuseBuild = <A, R, E>(
  self: Layer.Layer<A, never, R>,
  refusal: (cause: Cause.Cause<never>) => E,
): Layer.Layer<A, E, R> =>
  Layer.catchCause(self, (cause: Cause.Cause<never>) =>
    Layer.unwrap<A, never, R, E, never>(Effect.fail(refusal(cause))))

/** What one `cas daemon` invocation asks for, beyond the store's own
 * policy: the bind address, a one-invocation port override, the OTLP
 * export target, and the replica target the lag gauge reads. */
export interface DaemonOptions {
  readonly policy: ServePolicy
  readonly host: string
  readonly port: Option.Option<number>
  readonly otlp: Option.Option<string>
  readonly replicaTarget: Option.Option<string>
  /** Browser origins allowed to speak to this port. Empty means every
   * Origin-carrying request is refused — the MCP adapter's own
   * default, extended to the whole port. */
  readonly allowedOrigins?: ReadonlyArray<string> | undefined
  /** Host-header names accepted beyond loopback and the bound host —
   * the name a front proxy forwards, when it preserves the public
   * Host. */
  readonly allowedHosts?: ReadonlyArray<string> | undefined
}

/** The limits the daemon actually serves under, after the policy has
 * been ruled: the port that will bind, the clamped node cap, and the
 * two bounds honored per plane. */
export interface DaemonLimits {
  readonly port: number
  readonly maxNodeBytes: number
  readonly maxInFlight: number
  readonly maxBatchKeys: number
}

/**
 * The policy, read and ruled for HTTP. Refuses a credentialed policy
 * outright (the named non-goal); clamps `maxNodeBytes` under the body
 * cap with the same arithmetic as stdio, so the host's typed refusal
 * always fires before the transport's; says out loud which caps are in
 * force and that `maxInFlight` is per plane.
 */
export const applyDaemonPolicy = (
  options: DaemonOptions,
): Effect.Effect<DaemonLimits, CredentialedPolicyUndaemonable> =>
  Effect.gen(function* () {
    const policy = options.policy
    if (!policy.anonymousReads) {
      return yield* new CredentialedPolicyUndaemonable(
        policy.credentialEnv === undefined
          ? {}
          : { credentialEnv: policy.credentialEnv },
      )
    }
    const maxNodeBytes = Math.min(policy.maxNodeBytes, maxServableNodeBytes)
    if (maxNodeBytes !== policy.maxNodeBytes) {
      yield* Effect.logWarning("maxNodeBytes clamped under the transport frame cap").pipe(
        Effect.annotateLogs({
          configured: policy.maxNodeBytes,
          effective: maxNodeBytes,
          frameBytes: transportFrameBytes,
          reason:
            "an MCP payload crosses as hex, so 2 x maxNodeBytes + slack must stay under maxRequestBodySize — the clamp keeps mcp/NodeTooLarge firing before the transport's own refusal",
        }),
      )
    }
    const port = Option.getOrElse(options.port, () => policy.port)
    yield* Effect.logInfo("serve policy applied").pipe(
      Effect.annotateLogs({
        honored:
          `port=${port} maxNodeBytes=${maxNodeBytes} maxInFlight=${policy.maxInFlight} maxBatchKeys=${policy.maxBatchKeys}`,
        // Two planes, two gates: the store can see up to twice the
        // bound when both saturate. Stated at every startup so the
        // number in the config never reads as a whole-host promise.
        perPlane: `maxInFlight bounds EACH plane; worst case ${2 * policy.maxInFlight} store-touching calls`,
        frameCap: `${transportFrameBytes} bytes (maxRequestBodySize), slack ${frameSlackBytes}`,
        portOverridden: Option.isSome(options.port),
      }),
    )
    return {
      port,
      maxNodeBytes,
      maxInFlight: policy.maxInFlight,
      maxBatchKeys: policy.maxBatchKeys,
    }
  })

/** The wire policy the cas-http/0 core serves under: the ruled limits,
 * no credential (a credentialed policy refused at boot), reads open —
 * which is the only configuration this daemon serves. */
const wirePolicy = (limits: DaemonLimits): Server.Policy => ({
  maxBatchKeys: limits.maxBatchKeys,
  maxNodeBytes: limits.maxNodeBytes,
  anonymousReads: true,
})

/* ── the two planes ──────────────────────────────────────────────── */

/**
 * MCP over HTTP: the same toolkit, the same handler gate, a different
 * transport layer. `layerHttp` registers the POST route (and the 405s
 * around it) against the shared router; its only failure mode at the
 * pin is an empty protocol list, which `offeredProtocols` cannot be.
 */
const layerMcpPlane = (
  limits: HostLimits,
  allowedOrigins: ReadonlyArray<string>,
) =>
  McpServer.toolkit(casToolkit).pipe(
    Layer.provide(layerHandlers(limits)),
    Layer.provideMerge(
      McpServer.layerHttp({
        ...serverIdentity,
        path: mcpPath,
        protocols: offeredProtocols,
        // Defence in depth: the front door already refuses foreign
        // origins port-wide; the adapter checks its own route again.
        allowedOrigins,
      }).pipe(Layer.orDie),
    ),
  )

/**
 * cas-http/0, bound at last: the four-step shell over the semantic
 * core, registered as the port's wildcard. Static routes (`/mcp`,
 * `/metrics`) win over the wildcard in the router, so this plane
 * receives exactly the exchanges the profile governs — and answers
 * ALL of them, unknown paths and wrong methods included, from its own
 * status table. Store-touching requests pass an admission gate sized
 * `maxInFlight`; the capabilities read stays outside it.
 */
const layerCasPlane = (limits: DaemonLimits) =>
  Layer.effectDiscard(Effect.gen(function* () {
    const policy = wirePolicy(limits)
    const app = yield* Server.httpApp(policy)
    const gate = yield* Semaphore.make(limits.maxInFlight)
    const router = yield* HttpRouter.HttpRouter
    // The gauge's value, held where the gate holds it — the same
    // set-not-increment discipline as the MCP plane's gauge.
    let live = 0
    const mark = (delta: number): Effect.Effect<void> =>
      Effect.suspend(() => {
        live += delta
        return Metric.update(wireInflight, live)
      })
    const gated = gate.withPermits(1)(
      mark(1).pipe(
        Effect.andThen(app),
        Effect.onExit(() => mark(-1)),
      ),
    )
    yield* router.add("*", "/*", (request) =>
      request.url.split("?")[0] === capabilitiesPath ? app : gated)
  })).pipe(Layer.provide(Server.Core.layer(wirePolicy(limits))))

/* ── the front door: guard, time, log ────────────────────────────── */

/** A Host header's name, without its port and CASE-FOLDED:
 * `127.0.0.1:8080` → `127.0.0.1`, `[::1]:8080` → `[::1]`,
 * `Front.Example` → `front.example`. Folding happens here, which is
 * the one place both sides of every host comparison pass through —
 * the allowlist is built from it and every request is checked through
 * it, so insert and compare cannot disagree. */
const hostName = (header: string): string => {
  const folded = header.trim().toLowerCase()
  if (folded.startsWith("[")) {
    const closing = folded.indexOf("]")
    return closing >= 0 ? folded.slice(0, closing + 1) : folded
  }
  return folded.split(":")[0] ?? folded
}

/** An Origin as the allowlist keys it: case-folded whole. An origin's
 * scheme and host are both ASCII case-insensitive and an origin
 * carries no path, so folding the entire string is exact rather than
 * approximate. Same discipline as `hostName` — one function, both
 * sides. */
const originKey = (origin: string): string => origin.trim().toLowerCase()

/** The Host names always accepted: the rebinding check must never
 * refuse the addresses this host actually answers on. */
const loopbackHosts: ReadonlyArray<string> = [
  "127.0.0.1",
  "localhost",
  "::1",
  "[::1]",
]

/** What the front door decided about one request before any handler
 * ran. */
type DoorDecision =
  | { readonly _tag: "Pass"; readonly origin: string | undefined }
  | { readonly _tag: "Preflight"; readonly origin: string }
  | { readonly _tag: "RefusedHost"; readonly host: string }
  | { readonly _tag: "RefusedOrigin"; readonly origin: string }

/** An Origin's `host[:port]` half, case-folded, without parsing
 * exceptions: `http://App.Local:5173` → `app.local:5173`. An origin
 * that does not look like `scheme://…` (e.g. the literal `null`)
 * answers itself, which can then only match nothing. */
const originHost = (origin: string): string => {
  const folded = originKey(origin)
  const separator = folded.indexOf("://")
  return separator >= 0 ? folded.slice(separator + 3) : folded
}

/* ── refusals that say what to do about themselves ───────────────── */

/** What a refused or empty exchange is told: the defect named, the
 * fix named — the estate's grade-A bar held on the wire, not only in
 * the log. */
interface Refusal {
  readonly status: number
  readonly refused: string
  readonly why: string
  readonly fix: string
}

/**
 * One refusal, rendered in the media type of the plane that answers
 * it — a plane's content type is its law, and a body in the wrong one
 * is worse than no body.
 *
 * cas-http/0 is the deliberate exception and stays OCTET-BARE: the
 * profile's §1 makes every body on that plane
 * `application/octet-stream` under a closed binary framing, compared
 * exactly, so a JSON explanation there would be a profile violation
 * dressed as helpfulness. On that plane the STATUS is the whole
 * sentence — §1's status→event table is what a client decodes — and
 * the reason still reaches a person through the request log line.
 *
 * A refused browser gets no `access-control-allow-origin` (that IS
 * the refusal), so these bodies are read by curl, by launchers, and
 * by the operator reading a log — which is exactly who can act on the
 * fix.
 */
const refusedResponse = (
  plane: string,
  refusal: Refusal,
): HttpServerResponse.HttpServerResponse =>
  plane === "cas-http/0"
    ? HttpServerResponse.empty({ status: refusal.status })
    : plane === "metrics"
    ? HttpServerResponse.text(
      [
        `# refused: ${refusal.refused}`,
        `# why: ${refusal.why}`,
        `# fix: ${refusal.fix}`,
        "",
      ].join("\n"),
      { status: refusal.status, contentType: "text/plain; charset=utf-8" },
    )
    : HttpServerResponse.jsonUnsafe({
      refused: refusal.refused,
      why: refusal.why,
      fix: refusal.fix,
    }, { status: refusal.status })

/** A header value quoted back to its sender: control characters
 * dropped and the length capped. The value is the caller's own, so
 * echoing it gains an attacker nothing — but a response body is not
 * the place to carry an unbounded stranger's string, and the metrics
 * plane's rendering is line-oriented. */
const shown = (value: string): string =>
  Array.from(value.slice(0, 120), (character) => {
    const code = character.codePointAt(0) ?? 0
    return code < 0x20 || code === 0x7F ? " " : character
  }).join("")

/** The rebinding refusal, said to whoever asked. */
const hostRefusal = (host: string): Refusal => ({
  status: 403,
  refused: `the Host header names ${shown(host)}, which this daemon does not answer as`,
  why:
    "a DNS-rebinding request arrives at the loopback address wearing the attacker's own Host, so this daemon answers only to the names it was told it has: loopback, the address it bound, and every --allow-host entry",
  fix:
    "pass --allow-host <name> if the name is really this daemon's (a front proxy that preserves the public Host needs it), or have the proxy rewrite Host to the bound address",
})

/** The origin refusal, said to whoever asked. */
const originRefusal = (origin: string): Refusal => ({
  status: 403,
  refused: `the browser origin ${shown(origin)} is not allowed on this port`,
  why:
    "no origin is allowed by default — a page the operator never named may not script this daemon. Only --allow-origin entries and this daemon's own origin pass, and --allow-host does not widen that",
  fix:
    "pass --allow-origin <origin> to admit this page; non-browser clients send no Origin header and need nothing",
})

/** An artifact the emitters have not written. Not an error page: a
 * statement about the tree this daemon reads. */
const projectionMissing = (name: string): Refusal => ({
  status: 404,
  refused: `${name} has not been emitted`,
  why:
    "the daemon serves these artifacts and never authors them, so a missing one is a fact about the checkout it reads rather than a fault in the request",
  fix:
    "run the emitters (`mise run gen`); the file is served on the next request, with no restart",
})

const decideDoor = (
  request: HttpServerRequest.HttpServerRequest,
  allowedHosts: ReadonlySet<string>,
  ownHosts: ReadonlySet<string>,
  allowedOrigins: ReadonlySet<string>,
): DoorDecision => {
  // DNS rebinding arrives AT the loopback address carrying the
  // attacker's own Host; a request naming a host this daemon was not
  // told it answers as is refused before any plane sees it. A missing
  // Host is tolerated — every browser sends one, and the attack needs
  // a browser.
  const host = request.headers["host"]
  if (host !== undefined && !allowedHosts.has(hostName(host))) {
    return { _tag: "RefusedHost", host }
  }
  const origin = request.headers["origin"]
  // A SAME-ORIGIN request also carries an Origin on modern browsers'
  // POSTs: a page this daemon SERVED, talking back to it, passes
  // without an allowlist entry. The pattern is opencode's request
  // guard (`corpus/anomalyco_opencode/packages/server/src/cors.ts:22-26`),
  // which its own highest-risk surface (the pty WebSocket) relies on.
  //
  // The allowance is keyed to `ownHosts` — loopback and the bound
  // address — and NEVER to the --allow-host set. Keying it to the
  // whole Host allowlist made --allow-host grant origin trust
  // transitively: under an allowed public Host an unlisted browser
  // origin passed every plane and wrote bytes into the store, while
  // the banner said every browser Origin was refused. The two gates
  // are independent now, which is the only shape in which the banner
  // can be true.
  const sameOrigin = origin !== undefined
    && host !== undefined
    && ownHosts.has(hostName(host))
    && originHost(origin) === originKey(host)
  if (origin !== undefined && !sameOrigin && !allowedOrigins.has(originKey(origin))) {
    return { _tag: "RefusedOrigin", origin }
  }
  if (
    origin !== undefined
    && request.method === "OPTIONS"
    && request.headers["access-control-request-method"] !== undefined
  ) {
    return { _tag: "Preflight", origin }
  }
  return { _tag: "Pass", origin }
}

const preflightResponse = (
  request: HttpServerRequest.HttpServerRequest,
  origin: string,
): HttpServerResponse.HttpServerResponse =>
  HttpServerResponse.empty({ status: 204 }).pipe(
    HttpServerResponse.setHeaders({
      "access-control-allow-origin": origin,
      "access-control-allow-methods": "GET, PUT, POST, OPTIONS",
      "access-control-allow-headers": request.headers["access-control-request-headers"]
        ?? "content-type, accept, cas-profile, mcp-session-id, mcp-protocol-version",
      "access-control-max-age": "600",
      // The answer varies with all three request headers it reads —
      // allow-headers is echoed from the request — so a cache keyed on
      // origin alone could serve one page another page's header set.
      vary: "origin, access-control-request-method, access-control-request-headers",
    }),
  )

/** The CORS decoration an allowed browser origin earns on every
 * answer, session headers exposed so a browser MCP client can hold its
 * session. */
const corsHeaders = (origin: string) => ({
  "access-control-allow-origin": origin,
  "access-control-expose-headers": "mcp-session-id, mcp-protocol-version",
  vary: "origin",
})

/**
 * One global middleware, three duties in arrival order: refuse what
 * the security posture refuses (foreign Host, foreign Origin), answer
 * the CORS preflight for origins that were allowed in, and give EVERY
 * exchange — refused ones included — its one sequence-numbered
 * `request` log line and its duration observation. Refusals on the
 * planes themselves are responses from their status tables, never
 * errors, so a governed exchange always logs a status; a defect that
 * still escapes logs `unhandled`.
 */
const layerFrontDoor = (options: {
  readonly bindHost: string
  readonly allowedHosts: ReadonlyArray<string>
  readonly allowedOrigins: ReadonlyArray<string>
}): Layer.Layer<never, never, HttpRouter.HttpRouter> =>
  Layer.effectDiscard(Effect.gen(function* () {
    const router = yield* HttpRouter.HttpRouter
    // The names this daemon IS — loopback plus the address it bound.
    // Origin trust is derived from THESE and from --allow-origin;
    // --allow-host widens only which Host names are answered.
    const ownHosts = new Set([...loopbackHosts, hostName(options.bindHost)])
    const hosts = new Set([...ownHosts, ...options.allowedHosts.map(hostName)])
    const origins = new Set(options.allowedOrigins.map(originKey))
    let sequence = 0
    yield* router.addGlobalMiddleware((handler) =>
      Effect.flatMap(HttpServerRequest.HttpServerRequest, (request) => {
        const path = request.url.split("?")[0] ?? request.url
        const plane = planeOf(path)
        const decision = decideDoor(request, hosts, ownHosts, origins)
        // Captured as its own const so the narrowing survives into the
        // closure — a fallback `?? ""` here would be an empty
        // allow-origin header waiting to be emitted.
        const passOrigin = decision._tag === "Pass" ? decision.origin : undefined
        const answer = decision._tag === "Preflight"
          ? Effect.succeed(preflightResponse(request, decision.origin))
          : decision._tag === "RefusedHost"
          ? Effect.succeed(refusedResponse(plane, hostRefusal(decision.host)))
          : decision._tag === "RefusedOrigin"
          ? Effect.succeed(refusedResponse(plane, originRefusal(decision.origin)))
          : passOrigin === undefined
          ? handler
          : Effect.map(handler, (response) =>
            HttpServerResponse.setHeaders(response, corsHeaders(passOrigin)))
        return Clock.currentTimeMillis.pipe(
          Effect.flatMap((started) =>
            answer.pipe(
              Effect.onExit((exit) =>
                Clock.currentTimeMillis.pipe(
                  Effect.flatMap((ended) => {
                    const ms = ended - started
                    sequence += 1
                    return Metric.update(
                      Metric.withAttributes(requestDuration, { plane }),
                      Duration.millis(ms),
                    ).pipe(
                      Effect.andThen(Effect.logInfo("request").pipe(
                        Effect.annotateLogs({
                          seq: sequence,
                          plane,
                          method: request.method,
                          path,
                          status: Exit.isSuccess(exit) ? exit.value.status : "unhandled",
                          ms,
                          ...(decision._tag === "RefusedHost"
                            ? { refused: "host", host: decision.host }
                            : decision._tag === "RefusedOrigin"
                            ? { refused: "origin", origin: decision.origin }
                            : {}),
                        }),
                      )),
                    )
                  }),
                )),
            )),
        )
      }))
  }))

/* ── projections: the emitted artifacts, served ──────────────────── */

/**
 * The emitted JSON artifacts this daemon serves read-only — tier 0 of
 * the front end: a browser (or any agent) learns the estate's tool
 * vocabulary, surface, obligations, and environment from the same
 * byte-gated documents the gates check, over plain GETs. The daemon
 * never authors these; each is read from disk per request, so a
 * regenerated artifact is served without a restart. Absent artifacts
 * answer 404 — an un-emitted projection is a fact, not an error page.
 *
 * The plane exists by RULING: decision 32(a) released tier-0 serving
 * to the daemon, read-only. Before it, FRONTEND.md's tier-0 story was
 * a static host; the ruling moved it here, and FRONTEND.md says so.
 *
 * WHERE the files come from is a repo-checkout fact, honestly stated:
 * each source URL resolves relative to this file, and every one of the
 * seven now resolves through the `../../../cas/` segment, which in an
 * INSTALLED tree lands back in `@foldlab/cas`. Only `cas-tools.json` is
 * actually there, because `scripts/copy-mcp-manifest.ts` materializes
 * it; the other six are not shipped, so from a published tarball this
 * plane serves one of seven and answers 404 for the rest. That is now a
 * packaging question — WHICH emitted artifacts the distributable
 * carries — and no longer a structural one: before the M4 meta-home
 * migration, `environment.json` read from `docs/` and could not be
 * reached from inside a package at any depth. SERVING.md scopes the
 * claim to repo-checkout serving and carries the OWED row.
 *
 * The served NAMES are the wire surface and did NOT move with the
 * files. The migration retargeted every source path into
 * `library/cas/meta/out/`; renaming a served path is a protocol change,
 * not a file-layout one.
 *
 * WHY THESE PATHS ARE STILL WRITTEN OUT, after `bin/cli/ledgers.ts`
 * took its own from `MANIFEST.META.json` (D2 cutover): the fit is
 * genuinely bad here, for four reasons that compound.
 *
 * - Four of the seven are not on the meta plane at all — `cas-tools`
 *   is the MCP plane's, the two `schema-` documents are the schema
 *   index's, `schema-verdicts` is conformance's — so the registry has
 *   no row to give them and the list would end up half-derived.
 * - The three that ARE on it (surface, obligations, environment) are
 *   all `awaiting` rows. Deriving them buys a path and no shape,
 *   which is the half of the cutover with nothing in it.
 * - These resolve from `import.meta.url`, not from a lab root, and
 *   the manifest is NOT shipped in the published tarball. A derived
 *   list would serve zero projections from an installed tree where
 *   this one still serves `cas-tools.json` — a regression in exactly
 *   the deployment SERVING.md carries the OWED row for.
 * - `projectionSources` is a VALUE, and SERVING.md's drift gate reads
 *   it as one. Making it an effect would move that gate's authority
 *   from a static export to a runtime file read.
 *
 * The plane the daemon serves and the plane that registers emitted
 * artifacts are simply not the same plane. When the three meta rows
 * grow shapes, what they earn is a decode through `toEffectSchema` —
 * not a path from a registry that cannot reach half this list.
 */
export const projectionSources: ReadonlyArray<{
  readonly name: string
  readonly source: URL
}> = [
  { name: "cas-tools.json", source: new URL("../../../cas/mcp/cas-tools.json", import.meta.url) },
  { name: "cas-surface.json", source: new URL("../../../cas/meta/out/surface.META.json", import.meta.url) },
  { name: "cas-obligations.json", source: new URL("../../../cas/meta/out/obligations.META.json", import.meta.url) },
  { name: "schema-index.json", source: new URL("../../../cas/schemas/index.json", import.meta.url) },
  { name: "schema-addresses.json", source: new URL("../../../cas/schemas/addresses.json", import.meta.url) },
  { name: "schema-verdicts.json", source: new URL("../../../cas/conformance/schema-verdicts.json", import.meta.url) },
  { name: "environment.json", source: new URL("../../../cas/meta/out/environment.META.json", import.meta.url) },
]

const layerProjections: Layer.Layer<
  never,
  never,
  HttpRouter.HttpRouter | FileSystem.FileSystem | Path.Path
> = Layer.effectDiscard(Effect.gen(function* () {
  const router = yield* HttpRouter.HttpRouter
  const fs = yield* FileSystem.FileSystem
  const path = yield* Path.Path
  const resolved = yield* Effect.forEach(projectionSources, (entry) =>
    path.fromFileUrl(entry.source).pipe(
      Effect.map((file) => ({ name: entry.name, file })),
      Effect.orDie,
    ))
  for (const entry of resolved) {
    yield* router.add(
      "GET",
      `${projectionsPath}/${entry.name}`,
      fs.readFileString(entry.file).pipe(
        Effect.map((body) =>
          HttpServerResponse.text(body, {
            contentType: "application/json",
            headers: { "cache-control": "no-cache" },
          })),
        Effect.orElseSucceed(() =>
          refusedResponse("projections", projectionMissing(entry.name))),
      ),
    )
  }
  yield* router.add(
    "GET",
    projectionsPath,
    Effect.forEach(resolved, (entry) =>
      fs.exists(entry.file).pipe(
        Effect.orElseSucceed(() => false),
        Effect.map((present) => ({
          name: entry.name,
          path: `${projectionsPath}/${entry.name}`,
          present,
        })),
      )).pipe(
        Effect.map((projections) =>
          HttpServerResponse.jsonUnsafe({ projections }, {
            headers: { "cache-control": "no-cache" },
          })),
      ),
  )
}))

/* ── history: the store's own word, served ───────────────────────── */

/** The plane label `/history` answers under — its own, never
 * cas-http/0's. */
const historyPlane = "history"

/** The canonical decimal encodings of ℕ, one string per mark: no sign,
 * no leading zero, no exponent, no fraction, no whitespace.
 *
 * At the wire a query parameter IS a string, so this is a DECODE and
 * not a coercion — there is no `number` here to be lenient about. The
 * seam's own leniency (`flooredMark` floors a negative or fractional
 * mark) exists for a caller who already holds a number and stays
 * untouched; `?since=-5` answering the whole history would be exactly
 * the "silently answered a different question" hazard the receipts
 * plane must never commit. Refusing an alias like `01` also keeps the
 * accepted set in bijection with the marks, so one mark has one
 * spelling on this wire. */
const wireNumeral = /^(0|[1-9][0-9]*)$/u

/** The only query keys this route answers. */
const historyKeys: ReadonlyArray<string> = ["since", "limit"]

/** A parameter that is not a numeral. */
const notANumeral = (key: string, raw: string): Refusal => ({
  status: 400,
  refused: `${key}=${shown(raw)} is not a ${key === "limit" ? "page limit" : "mark"}`,
  why:
    `at the wire a parameter is a string, so it is decoded rather than coerced: this route accepts the canonical decimal spelling of a whole number up to ${Number.MAX_SAFE_INTEGER} and nothing else — no sign, no leading zero, no fraction, no exponent, no spaces`,
  fix: key === "limit"
    ? `ask for ?limit=<n> with n at least 1 and at most ${Cas.wordLogPageLimit}, or leave it out for the default page`
    : "ask for ?since=<mark>, a zero-based count of receipts — 0 is the whole history, and a later read starts from the `next` the previous one answered",
})

/** A key this route does not answer. `from`/`to` are held out on SCOPE
 * and say so — `since`+`limit` already is a ranged read, and widening
 * it is a ruling rather than an implementation choice. Everything else
 * is the address-not-value line: the server executes what answers an
 * ADDRESS and nothing whose answer is a computed VALUE. */
const unknownKey = (key: string): Refusal =>
  key === "from" || key === "to"
    ? {
      status: 400,
      refused: `?${key}= is not answered on this route yet`,
      why:
        "a closed window is a capability this route already has the arithmetic for — `since` is the start and `limit` is the width — so a second spelling of it is deferred on scope, not refused on principle",
      fix: "read the window as ?since=<from>&limit=<to − from>",
    }
    : {
      status: 400,
      refused: `?${shown(key)}= is not a parameter of this route`,
      why:
        "this route answers word-INDEX arithmetic only — a mark and a page bound. A predicate over a receipt's FIELDS is a computed value, and a route that silently IGNORED one would hand back an unfiltered page the client believes was filtered, which is worse than refusing",
      fix:
        "read the page with ?since=<mark>&limit=<n> and fold the receipts on your own side; the parameters this route answers are `since` and `limit`",
    }

/** One key, twice. Answering either value silently answers a question
 * that was not asked, so the door refuses rather than picking. */
const repeatedKey = (key: string): Refusal => ({
  status: 400,
  refused: `?${key}= was given more than once`,
  why:
    "two values for one parameter is two different questions, and answering either of them silently would be answering the one this route chose rather than the one that was asked",
  fix: `send ?${key}= exactly once`,
})

/** The word log's own refusal, carried out to the wire with its text
 * intact — the seam names the defect and the fix already, and
 * restating it here would be a second, weaker voice. */
const seamRefusal = (reason: string): Refusal => ({
  status: 400,
  refused: "the word log refused this read",
  why: reason,
  fix:
    "read the whole history from mark 0, or resume from the `next` a previous read answered",
})

/** The wrong verb on the right path — the CO-TENANT's 405, never the
 * profile's 400. PROFILE §14: the status table "does not answer
 * exchanges inside a declared co-tenant prefix", and `/mcp`'s row
 * shows the shape. */
const methodRefused = (method: string): Refusal => ({
  status: 405,
  refused: `${shown(method)} is not a method this route answers`,
  why:
    "the word is read-only on this plane: history is a fact the store already recorded, and nothing writes it over HTTP. Admission happens through `cas put`, the MCP tool plane, or the cas-http/0 byte plane, and the receipt follows it",
  fix: `GET ${historyPath}?since=<mark>&limit=<n>`,
})

/** What the door made of one request's query string: the decoded
 * parameters, or the refusal that stopped it. */
type HistoryQuery =
  | { readonly _tag: "Decoded"; readonly since: number; readonly limit: number | undefined }
  | { readonly _tag: "Refused"; readonly refusal: Refusal }

/**
 * The query string, decoded totally and FAIL-CLOSED.
 *
 * Fail-closed is the whole contract here, and it is stronger than "no
 * parameter filters by receipt field" on purpose: that is a claim
 * about BEHAVIOUR, and an implementation that silently ignores `?tag=1`
 * satisfies it while being strictly worse than one that refuses — the
 * client believes it received a filtered answer and folds a lie. The
 * contract is therefore the DOOR, which also means the line holds
 * against future creep with no further ruling: the day someone adds
 * `?column=`, this function already says no.
 */
const decodeHistoryQuery = (url: string): HistoryQuery => {
  const mark = url.indexOf("?")
  const parameters = new URLSearchParams(mark < 0 ? "" : url.slice(mark + 1))
  const seen = new Set<string>()
  for (const key of parameters.keys()) {
    if (!historyKeys.includes(key)) {
      return { _tag: "Refused", refusal: unknownKey(key) }
    }
    if (seen.has(key)) return { _tag: "Refused", refusal: repeatedKey(key) }
    seen.add(key)
  }
  const decoded: Record<string, number> = {}
  for (const key of historyKeys) {
    const raw = parameters.get(key)
    if (raw === null) continue
    if (!wireNumeral.test(raw) || Number(raw) > Number.MAX_SAFE_INTEGER) {
      return { _tag: "Refused", refusal: notANumeral(key, raw) }
    }
    decoded[key] = Number(raw)
  }
  // `since` absent is mark 0 — the whole history (W2 `since_zero`).
  // `limit` absent is left absent, so the SEAM's own default applies
  // and there is exactly one page bound in the system rather than a
  // second one declared here.
  return { _tag: "Decoded", since: decoded["since"] ?? 0, limit: decoded["limit"] }
}

/**
 * `GET /history?since&limit` — the store's word over HTTP, read-only.
 *
 * The document is the REGISTERED one: `wordHistorySchema`'s encoding,
 * canonically printed, which is byte for byte what `cas history --json`
 * prints at the same mark. Two registers, one document — and the
 * printing path is literally the CLI's, so the two cannot drift into
 * agreement-by-coincidence.
 *
 * Everything this route does NOT do is as ruled as what it does: no
 * validator (no `etag`, no `last-modified`, no `304` — cut, and the
 * cut is gated, because the log's own truncation repair moves `next`
 * BACKWARD and a cached validator would then be stale-but-fresh-
 * looking); no `hasMore` or `total` or tip beside `next`, because the
 * wire record is emitted from `Cas/Lang/WordWire.lean` and byte-gated,
 * so a field is an emitter change and a different slice; no write verb
 * of any kind; no repair of a damaged log on read.
 *
 * An empty word answers 200 with `{"next":0,"word":[]}` and never 404:
 * "no history yet" and "no route here" must not be the same sentence
 * to a client.
 */
const historyAnswer = (
  log: Cas.WordLogShape,
  request: HttpServerRequest.HttpServerRequest,
): Effect.Effect<HttpServerResponse.HttpServerResponse> => {
  if (request.method !== "GET") {
    return Effect.succeed(HttpServerResponse.setHeaders(
      refusedResponse(historyPlane, methodRefused(request.method)),
      { allow: "GET" },
    ))
  }
  const query = decodeHistoryQuery(request.url)
  if (query._tag === "Refused") {
    return Effect.succeed(refusedResponse(historyPlane, query.refusal))
  }
  // The door decoded, so the read is attempted; a parameter that did
  // not decode never reaches the log at all.
  return log.since(query.since, query.limit).pipe(
    Effect.match({
      onFailure: (failure) =>
        refusedResponse(historyPlane, seamRefusal(failure.reason)),
      onSuccess: (history) =>
        HttpServerResponse.text(
          canonicalJson(Schema.encodeSync(wordHistorySchema)(history)),
          {
            contentType: "application/json",
            // The same posture the sibling co-tenant keeps. A caching
            // intermediary in front of a polled feed would serve a
            // stale word to a client that cannot tell; whether this
            // route should ever carry a validator is UNRULED and
            // deliberately untested here.
            headers: { "cache-control": "no-cache" },
          },
        ),
    }),
  )
}

const layerHistory: Layer.Layer<
  never,
  never,
  HttpRouter.HttpRouter | Cas.WordLog
> = Layer.effectDiscard(Effect.flatMap(
  Effect.all([HttpRouter.HttpRouter, Cas.WordLog]),
  ([router, log]) =>
    router.add("*", historyPath, (request) => historyAnswer(log, request)),
))

/* ── the vitals sampler ──────────────────────────────────────────── */

/** How often process vitals are read. */
export const vitalsSampleInterval: Duration.Duration = Duration.seconds(5)

/** Resident memory, sampled for as long as the daemon lives — the
 * sensor for what cannot be bounded from inside (see `rssBytes`). */
const layerRss: Layer.Layer<never> = Layer.effectDiscard(
  Effect.forkScoped(Effect.forever(
    Effect.suspend(() => Metric.update(rssBytes, process.memoryUsage().rss)).pipe(
      Effect.andThen(Effect.sleep(vitalsSampleInterval)),
    ),
  )),
)

/* ── the replica lag sampler ─────────────────────────────────────── */

/** How often the replica directory is examined. Freshness at 5 s
 * granularity is plenty for a gauge whose alert threshold is minutes. */
export const replicaSampleInterval: Duration.Duration = Duration.seconds(5)

/** A replica target as it may be LOGGED: any `user:password@`
 * userinfo removed. litestream targets are usually plain paths or
 * bucket URLs, but the URL forms admit credentials, and a log line is
 * a sink that outlives the process and travels to the hoover. */
const loggableTarget = (target: string): string =>
  target.replace(/\/\/[^/@\s]*@/u, "//<redacted>@")

/** A litestream target this host can stat: a plain path or a
 * `file://` URL. Anything with another scheme (s3, abs, sftp) is real
 * but not locally measurable — litestream's own metrics endpoint is
 * the sensor there, and the log says so. */
const localReplicaPath = (target: string): Option.Option<string> =>
  target.startsWith("file://")
    ? Option.some(target.slice("file://".length))
    : target.includes("://")
    ? Option.none()
    : Option.some(target)

/** The newest mtime under the replica directory, as epoch ms. The
 * replica advances by writing WAL segment files, so the newest file IS
 * the last replication. An unreadable or absent directory answers
 * none — a replica that has never been written is unmeasured, not
 * fresh. */
const newestReplicaWrite = (
  directory: string,
): Effect.Effect<Option.Option<number>, never, FileSystem.FileSystem | Path.Path> =>
  Effect.gen(function* () {
    const fs = yield* FileSystem.FileSystem
    const path = yield* Path.Path
    const nothing: ReadonlyArray<string> = []
    const entries = yield* fs.readDirectory(directory, { recursive: true }).pipe(
      Effect.orElseSucceed(() => nothing),
    )
    let newest = Option.none<number>()
    for (const entry of entries) {
      const info = yield* fs.stat(path.join(directory, entry)).pipe(
        Effect.asSome,
        Effect.orElseSucceed(() => Option.none<FileSystem.File.Info>()),
      )
      if (Option.isNone(info) || info.value.type !== "File") continue
      const mtime = info.value.mtime
      if (Option.isNone(mtime)) continue
      const ms = mtime.value.getTime()
      newest = Option.some(Option.match(newest, {
        onNone: () => ms,
        onSome: (held) => Math.max(held, ms),
      }))
    }
    return newest
  })

/** One sample: gauge = now − newest replica write, or `-1` when there
 * is nothing to measure. */
const sampleReplica = (
  directory: string,
): Effect.Effect<void, never, FileSystem.FileSystem | Path.Path> =>
  newestReplicaWrite(directory).pipe(
    Effect.flatMap((newest) =>
      Clock.currentTimeMillis.pipe(
        Effect.flatMap((now) =>
          Metric.update(
            replicaAge,
            Option.match(newest, {
              onNone: () => -1,
              onSome: (written) => Math.max(0, now - written),
            }),
          )),
      )),
  )

/**
 * The lag gauge's layer. Where the config names a local target, a
 * forked sampler keeps the gauge fresh for as long as the daemon
 * lives; where it names none — or names a remote one — the gauge says
 * `-1` and one startup line says why, so "unmeasured" is always a
 * statement and never a silent zero.
 */
export const layerReplicaLag = (
  target: Option.Option<string>,
): Layer.Layer<never, never, FileSystem.FileSystem | Path.Path> =>
  Option.match(target, {
    onNone: () =>
      Layer.effectDiscard(
        Metric.update(replicaAge, -1).pipe(
          Effect.andThen(Effect.logInfo("replica lag unmeasured").pipe(
            Effect.annotateLogs({
              reason: "config.json names no backup.target",
            }),
          )),
        ),
      ),
    onSome: (raw) =>
      Option.match(localReplicaPath(raw), {
        onNone: () =>
          Layer.effectDiscard(
            Metric.update(replicaAge, -1).pipe(
              Effect.andThen(Effect.logInfo("replica lag unmeasured").pipe(
                Effect.annotateLogs({
                  target: loggableTarget(raw),
                  reason:
                    "the target is not a local path — scrape litestream's own metrics endpoint for remote replica lag",
                }),
              )),
            ),
          ),
        onSome: (directory) =>
          Layer.effectDiscard(
            Metric.update(replicaAge, -1).pipe(
              Effect.andThen(Effect.logInfo("replica lag measured").pipe(
                Effect.annotateLogs({
                  target: loggableTarget(directory),
                  sampleMs: Duration.toMillis(replicaSampleInterval),
                }),
              )),
              Effect.andThen(Effect.forkScoped(Effect.forever(
                sampleReplica(directory).pipe(
                  Effect.andThen(Effect.sleep(replicaSampleInterval)),
                ),
              ))),
            ),
          ),
      }),
  })

/* ── the composition ─────────────────────────────────────────────── */

/** The startup banner: the bound address (the ACTUAL one, so an
 * ephemeral-port boot still names its port), the planes, the offered
 * protocol revisions, and the caps in force. The one line an agent
 * reads to know what this process is. */
const layerBanner = (
  limits: DaemonLimits,
  options: DaemonOptions,
): Layer.Layer<never, never, HttpServer.HttpServer> =>
  Layer.effectDiscard(
    Effect.flatMap(HttpServer.HttpServer, (server) =>
      Effect.logInfo("daemon serving").pipe(
        Effect.annotateLogs({
          address: HttpServer.formatAddress(server.address),
          planes:
            `cas-http/0=wildcard mcp=${mcpPath} metrics=${metricsPath} projections=${projectionsPath} history=${historyPath}`,
          protocols: offeredProtocols
            .map((protocol) => protocol.protocolVersion)
            .join(","),
          policy:
            `maxNodeBytes=${limits.maxNodeBytes} maxInFlight=${limits.maxInFlight}/plane maxBatchKeys=${limits.maxBatchKeys}`,
          // The enforced truth, not the intended one: this daemon's
          // own origin always passes (a page it served, talking back),
          // and --allow-host never widens the set. Saying "every
          // browser Origin refused" was the banner half of the
          // transitive-trust defect.
          origins: (options.allowedOrigins ?? []).length === 0
            ? "none configured (only this daemon's own origin passes; every other browser Origin is refused)"
            : `${(options.allowedOrigins ?? []).join(",")} (plus this daemon's own origin)`,
          extraHosts: (options.allowedHosts ?? []).length === 0
            ? "none"
            : (options.allowedHosts ?? []).join(","),
          otlp: Option.getOrElse(options.otlp, () => "off"),
          // Announced so a reader knows what silence means: a gap wider
          // than this in the heartbeat stream is the host stalled.
          heartbeatMs: Duration.toMillis(heartbeatInterval),
        }),
      )),
  )

/** How often a continuing export failure is repeated. One minute is
 * the exporter's own disable window, so a long outage is one line a
 * minute rather than a flood — and the first failure is always said. */
export const otlpWarnInterval: Duration.Duration = Duration.minutes(1)

/**
 * The export client, watched.
 *
 * The upstream exporter answers a dead collector by disabling itself
 * for 60 s and logging that at DEBUG
 * (`OtlpExporter.ts:220-224` at the pin); this host's stderr logger is
 * Info-and-above, so the line never lands and an operator who passed
 * `--otlp` watches a healthy daemon export nothing, in silence. That
 * is the whole defect: not that the export fails, but that failing is
 * indistinguishable from working.
 *
 * So the client the exporter is handed is wrapped here. A transport
 * failure or a non-2xx answer (the exporter applies its own
 * `filterStatusOk` ABOVE this wrapper, so a 500 arrives here as a
 * successful response with a status) says so once at WARNING, then at
 * most once per `otlpWarnInterval`. `/metrics` is untouched by any of
 * it: scraping is pull, and it keeps working while the push is down.
 */
const layerWatchedExportClient = (
  baseUrl: string,
): Layer.Layer<HttpClient.HttpClient, never, HttpClient.HttpClient> =>
  Layer.effect(
    HttpClient.HttpClient,
    Effect.gen(function* () {
      const client = yield* HttpClient.HttpClient
      let warnedAt = Option.none<number>()
      const warn = (detail: string): Effect.Effect<void> =>
        Clock.currentTimeMillis.pipe(
          Effect.flatMap((now) =>
            Option.isSome(warnedAt)
              && now - warnedAt.value < Duration.toMillis(otlpWarnInterval)
              ? Effect.void
              : Effect.sync(() => {
                warnedAt = Option.some(now)
              }).pipe(
                Effect.andThen(
                  Effect.logWarning("otlp export failing").pipe(
                    Effect.annotateLogs({
                      baseUrl,
                      detail,
                      effect:
                        "telemetry is not reaching the collector; /metrics still scrapes",
                      repeatMs: Duration.toMillis(otlpWarnInterval),
                    }),
                  ),
                ),
              )
          ),
        )
      return HttpClient.transformResponse(client, (response) =>
        response.pipe(
          Effect.tapError((error) => warn(`transport: ${error.reason}`)),
          Effect.tap((answered) =>
            answered.status >= 400
              ? warn(`collector answered ${answered.status}`)
              : Effect.void
          ),
        ))
    }),
  )

/** The OTLP export, when a wire is named: logs, metrics, and the spans
 * the estate's `Effect.fn` sites already carry, as OTLP/JSON over the
 * platform's HTTP client. Off by default — an export target is an
 * invocation's choice, never a config surprise. A failing export is
 * audible (see `layerWatchedExportClient`). */
const layerOtlp = (
  otlp: Option.Option<string>,
): Layer.Layer<never> =>
  Option.match(otlp, {
    onNone: () => Layer.empty,
    onSome: (baseUrl) =>
      Otlp.layerJson({
        baseUrl,
        resource: {
          serviceName: `${serverIdentity.name}-daemon`,
          serviceVersion: serverIdentity.version,
        },
      }).pipe(
        Layer.provide(
          layerWatchedExportClient(baseUrl).pipe(Layer.provide(FetchHttpClient.layer)),
        ),
      ),
  })

/**
 * The whole daemon as one layer: gate on the manifest, rule the
 * policy, then bind both planes, the metrics route, the request log,
 * the heartbeat, the replica gauge, and the banner on one Bun server.
 * The store services stay requirements — `bin/cli/daemon.ts` provides
 * them from the resolved store, exactly as every other verb's
 * composition does.
 *
 * A refusal here is the invocation's refusal: nothing is served by a
 * host that cannot prove it serves the emitted table, and nothing is
 * served open that the store's own policy says to gate.
 */
export const layerDaemon = (options: DaemonOptions) =>
  Layer.unwrap(Effect.gen(function* () {
    yield* gateOnManifest
    const limits = yield* applyDaemonPolicy(options)
    const allowedOrigins = options.allowedOrigins ?? []
    // The adapter's own origin check is a static list, so the front
    // door's dynamic own-origin allowance is taught to it explicitly:
    // the daemon's own origin, in its loopback spellings, joins the
    // adapter list when the port is fixed. (On an ephemeral port —
    // tests — the origin is unknowable before the bind; the front door
    // still admits same-origin, and only the /mcp route is stricter.)
    // Case-folded on the way in, because the adapter compares its own
    // list literally and a browser sends a lowercase Origin: an
    // operator's `--allow-origin http://Front.Example` would pass the
    // front door and then be refused by /mcp alone.
    const folded = allowedOrigins.map((origin) => originKey(origin))
    const adapterOrigins = limits.port === 0
      ? folded
      : [
        ...folded,
        `http://${hostName(options.host)}:${limits.port}`,
        `http://localhost:${limits.port}`,
        `http://127.0.0.1:${limits.port}`,
      ]
    const application = Layer.mergeAll(
      layerMcpPlane({
        maxNodeBytes: limits.maxNodeBytes,
        maxInFlight: limits.maxInFlight,
      }, adapterOrigins),
      layerCasPlane(limits),
      layerProjections,
      layerHistory,
      PrometheusMetrics.layerHttp({ path: metricsPath }),
      layerFrontDoor({
        bindHost: options.host,
        allowedHosts: options.allowedHosts ?? [],
        allowedOrigins,
      }),
    )
    return HttpRouter.serve(application, {
      // The front door's request line is the request logger — one
      // line, one vocabulary, sequence-numbered; the middleware logger
      // would be a second voice saying less.
      disableLogger: true,
      disableListenLog: true,
    }).pipe(
      Layer.merge(layerBanner(limits, options)),
      Layer.provide(refuseBuild(
        BunHttpServer.layer({
          port: limits.port,
          hostname: options.host,
          // The transport's own cap, pinned to the same number as
          // stdio's frame cap so the clamp arithmetic is one discipline.
          // Bun answers an oversized body with an HTTP refusal — on this
          // transport nothing is silently lost even past the cap. This
          // is also the TOTAL-body bound the stdio transport lacks: a
          // `cas_run` whose whole document exceeds the frame is refused
          // here, where stdio would lose it.
          maxRequestBodySize: transportFrameBytes,
          // Slow-loris posture, and the measured truth: this value does
          // NOT take at the pinned Bun. Connections are closed after
          // 12.0 s whatever is passed here (measured; Bun's own
          // documented default is 10 s, which it does not use either).
          // The number stands as the intent for a Bun that honors it;
          // the bound in force today is the platform's, and SERVING.md
          // says so rather than repeating a 30 that does not reproduce.
          idleTimeout: 30,
          // SIGTERM/SIGINT drain: stop accepting, let in-flight requests
          // finish, force-close at the deadline.
          gracefulShutdownTimeout: Duration.seconds(10),
        }),
        (cause) => {
          const diagnosis = bindDiagnosis(options.host, limits.port)
          return new DaemonBindRefused({
            host: options.host,
            port: limits.port,
            condition: diagnosis.condition,
            fix: diagnosis.fix,
            platformSaid: causeLine(cause),
          })
        },
      )),
      Layer.merge(layerHeartbeat),
      Layer.merge(layerRss),
      Layer.merge(layerReplicaLag(options.replicaTarget)),
      Layer.merge(layerOtlp(options.otlp)),
    )
  }))
