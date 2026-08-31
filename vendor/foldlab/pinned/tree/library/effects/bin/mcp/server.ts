/**
 * The MCP host — the consumer the emitted manifest never had.
 *
 * ## Transport
 *
 * stdio, newline-delimited JSON-RPC: the MCP default, and the only
 * transport a client can launch without a network. Effect's own MCP
 * support at the pinned version (`effect/unstable/ai/McpServer`) is
 * what serves it, so this package admits no new dependency to speak
 * the protocol — the protocol adapters, the JSON-RPC framing, the
 * `initialize` handshake, and `tools/list` / `tools/call` are Effect's,
 * and what is written here is the tool table and the handlers.
 *
 * Four protocol revisions are offered, newest first. The client names
 * one at `initialize`; a client naming a revision this host does not
 * hold gets the first — the newest — which is the adapter list's
 * documented fallback.
 *
 * Closing stdin IS the client's disconnect: the transport interrupts
 * the host when the stream ends, which is how a client that launched
 * this process as a child shuts it down. It also means a caller who
 * pipes a fixed file into `cas serve` and closes it immediately can
 * see the shutdown outrace its own replies. That is the transport's
 * contract and not a defect — a client holds the pipe open for as
 * long as it wants answers.
 *
 * ## Logs go to stderr, always
 *
 * On stdio the protocol IS stdout. A log line written there is a
 * corrupt frame, so the host installs a logger over `console.error`
 * before anything else and never writes to stdout itself. The format
 * is logfmt with the fiber's annotations, so the tool, the address,
 * and the outcome of every call are readable as fields — which is what
 * "an agent can tell what happened" has to mean for a machine reader.
 * How much is said is the CLI runner's own built-in `--log-level`
 * global flag, which sets `References.MinimumLogLevel`; no second flag
 * by that name is declared here.
 *
 * ## The `ServePolicy`, honored and refused
 *
 * `cas init` writes a `ServePolicy` into every store's `config.json`.
 * It was written for cas-http/0 and describes a wire; stdio is not
 * one. Rather than pretend, each field is ruled explicitly:
 *
 * - `maxNodeBytes` — HONORED, and CLAMPED. A cap on the payload of an
 *   admitted node is transport-independent, so it is enforced on
 *   `cas_put` and on every instruction of `cas_run`, refused with its
 *   own clause. It is also clamped under the transport's own frame
 *   cap — see "The frame cap" below.
 * - `maxInFlight` — HONORED. A bound on how many store-touching calls
 *   run at once, applied as one semaphore in `handlers.ts`. Work is
 *   work on every transport, so like `maxNodeBytes` it means the same
 *   thing here as it would on a wire.
 * - `port` — NOT APPLICABLE. stdio binds nothing. Reported at startup
 *   as ignored, so the number in the config never reads as a promise.
 * - `maxBatchKeys` — NOT APPLICABLE. It caps a cas-http/0 batch READ,
 *   and the manifest declares no batch-read tool. `cas_run` is a batch
 *   of admissions, not of keys, and capping it with this number would
 *   be a different limit wearing the same name.
 * - `anonymousReads` / `credentialEnv` — NOT APPLICABLE, and this is
 *   the one that REFUSES rather than warns. Over stdio the peer is the
 *   process that launched this one; there is no wire to present a
 *   credential on and nothing to check it against. A store whose
 *   policy says reads require a credential therefore does not get
 *   served over stdio at all — serving it anyway would answer reads
 *   the store's own configuration says to gate.
 *
 * ## The frame cap (BS-1, ruling R1(b))
 *
 * The NDJSON framing under `McpServer.layerStdio` refuses a line over
 * 16 MiB by THROWING `MaxBufferSizeExceeded` inside the transport's
 * own stream. The throw is sandboxed, logged, and retried — and the
 * client is never answered. An oversized request is not refused, it is
 * LOST, and a client without a timeout waits for it forever. The knob
 * is not reachable from here: `mcpStdioSerialization` builds its
 * NDJSON parser with no options, so the 16 MiB default stands.
 *
 * What IS reachable is the order the two caps fire in. A payload
 * crosses the wire as HEX — two characters per byte — so a node of
 * `maxNodeBytes` bytes occupies `2 × maxNodeBytes` characters plus the
 * document around it. Keep `2 × maxNodeBytes + slack` under 16 MiB and
 * this host's own `mcp/NodeTooLarge` always fires first, which turns a
 * silent loss into a typed refusal carrying its clause. A policy that
 * asks for more than that is CLAMPED to the largest cap that keeps the
 * property, and says so at WARN, because a store that cannot be served
 * within its own configured cap is still better served than lost.
 *
 * One honest limit on the claim: the discipline is per NODE, not per
 * FRAME. A `cas_run` carrying many within-cap instructions can still
 * build a frame over 16 MiB, and that frame is still lost. Bounding a
 * run's total size is a different limit and is not minted here.
 */
import { Duration, Effect, FileSystem, Layer, Logger, Path, Schema } from "effect"
import { McpProtocol, McpServer } from "effect/unstable/ai"
import { defaultServePolicy, type ServePolicy } from "../cli/store.ts"
import { layerHandlers } from "./handlers.ts"
import {
  assertAgreement,
  type ManifestDisagreement,
  type ManifestUnavailable,
  manifestPath,
  readManifest,
} from "./manifest.ts"
import { heartbeatInterval, layerHeartbeat } from "./telemetry.ts"
import { casToolkit, servedTools } from "./tools.ts"

/** What the client sees at `initialize`. The version is the package's,
 * so a client can tell one build of the host from another. */
export const serverIdentity = {
  name: "cas",
  version: "0.1.0",
  description:
    "a content-addressed store as a data structure — admit nodes, load them back, run straight-line programs, publish and list roots",
} as const

/**
 * The logger every `cas serve` invocation installs: logfmt over
 * `console.error`. stdout belongs to the protocol.
 */
export const layerStderrLogs: Layer.Layer<never> = Logger.layer([
  Logger.withConsoleError(Logger.formatLogFmt),
])

/** The protocol revisions this host offers, newest first — one list,
 * shared by every transport, so stdio and the daemon cannot drift. A
 * client naming a revision outside it gets the first, which is the
 * adapter list's documented fallback. */
export const offeredProtocols = [
  McpProtocol.v2025_11_25,
  McpProtocol.v2025_06_18,
  McpProtocol.v2025_03_26,
  McpProtocol.v2024_11_05,
] as const

/** A store whose policy gates reads has no stdio spelling. */
export class CredentialedPolicyUnservable
  extends Schema.TaggedError<CredentialedPolicyUnservable>()(
    "mcp/CredentialedPolicyUnservable",
    { credentialEnv: Schema.optionalKey(Schema.String) },
  )
{
  override get message(): string {
    return [
      "this store's serve policy requires a credential for reads, and stdio cannot check one",
      this.credentialEnv === undefined
        ? "  config.json says anonymousReads: false"
        : `  config.json says anonymousReads: false, credentialEnv: ${this.credentialEnv}`,
      "  stdio's peer is the process that launched this one — there is no wire to authenticate",
      "  set anonymousReads: true to serve this store over stdio",
    ].join("\n")
  }
}

/** The transport's own frame cap: `RpcSerialization`'s NDJSON default,
 * which `McpServer.layerStdio` builds with no options and this host
 * therefore cannot configure. Restated here as the number the clamp is
 * computed against, and asserted against the transport by
 * `test/McpBackpressure.test.ts`. */
export const transportFrameBytes = 16 * 1024 * 1024

/** What a node's document costs around its payload: the JSON-RPC
 * envelope, the tool name, the version/tag/refs fields, and the
 * quoting. Sixty-four kilobytes is far more than any of it and leaves
 * the arithmetic obviously safe rather than exactly tight. */
export const frameSlackBytes = 64 * 1024

/** The largest `maxNodeBytes` for which this host's own cap still
 * fires before the transport's. A payload crosses as hex, so a byte of
 * node costs two characters of frame. */
export const maxServableNodeBytes: number = Math.floor(
  (transportFrameBytes - frameSlackBytes) / 2,
)

/** The limits the handlers enforce, after the policy has been ruled. */
export interface HostLimits {
  readonly maxNodeBytes: number
  readonly maxInFlight: number
}

/**
 * The policy, read and ruled. Answers the limits the handlers enforce;
 * refuses outright when the policy asks for something stdio cannot
 * give; clamps the one number that could otherwise let the transport
 * lose a request instead of refusing it; says out loud, once, which
 * numbers it is ignoring and which caps are actually in force.
 */
export const applyServePolicy = (
  policy: ServePolicy,
): Effect.Effect<HostLimits, CredentialedPolicyUnservable> =>
  Effect.gen(function* () {
    if (!policy.anonymousReads) {
      return yield* new CredentialedPolicyUnservable(
        policy.credentialEnv === undefined ? {} : { credentialEnv: policy.credentialEnv },
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
            "a payload crosses as hex, so 2 x maxNodeBytes + slack must stay under the frame cap — above it the transport loses the request instead of refusing it",
        }),
      )
    }
    yield* Effect.logInfo("serve policy applied").pipe(
      Effect.annotateLogs({
        // The caps actually in force, as numbers, at every startup:
        // the whole point of the clamp is that a reader can see which
        // refusal a client will get, and from which cap.
        honored: `maxNodeBytes=${maxNodeBytes} maxInFlight=${policy.maxInFlight}`,
        frameCap: `${transportFrameBytes} bytes, slack ${frameSlackBytes}`,
        // Named, not silently dropped: a number in the config that
        // this transport does not use is a false affordance unless
        // the host says so every time it starts.
        notApplicable: `port=${policy.port} maxBatchKeys=${policy.maxBatchKeys}`,
        reason: "stdio binds no port and serves no batch read",
      }),
    )
    return { maxNodeBytes, maxInFlight: policy.maxInFlight }
  })

/**
 * THE BOOT GATE: read the emitted manifest and compare it to the table
 * this host serves. Run ahead of the transport on purpose — a host
 * that would answer `tools/list` with a table the estate did not emit
 * must never reach `initialize`.
 */
export const gateOnManifest: Effect.Effect<
  void,
  ManifestUnavailable | ManifestDisagreement,
  FileSystem.FileSystem | Path.Path
> = Effect.gen(function* () {
  const path = yield* manifestPath
  const manifest = yield* readManifest(path)
  yield* assertAgreement(manifest, servedTools)
  yield* Effect.logInfo("manifest agreed").pipe(
    Effect.annotateLogs({
      manifest: path,
      manifestVersion: manifest.manifestVersion,
      schemaRevision: manifest.schemaRevision,
      tools: manifest.tools.map((tool) => tool.name).join(","),
    }),
  )
})

/**
 * The served composition: the gate, then the tool table registered
 * against a stdio MCP server. The store services stay requirements —
 * `bin/cli/commands.ts` provides them from the resolved store, exactly
 * as it does for every other verb.
 */
export const layerServeStdio = (limits: HostLimits) =>
  McpServer.toolkit(casToolkit).pipe(
    Layer.provide(layerHandlers(limits)),
    // The heartbeat starts with the host and is interrupted with it.
    // It is merged rather than provided because it answers nothing —
    // it is the one fiber whose OUTPUT is the absence of its output.
    Layer.provideMerge(layerHeartbeat),
    Layer.provideMerge(McpServer.layerStdio({
      ...serverIdentity,
      protocols: offeredProtocols,
    })),
  )

/**
 * The whole host as one layer: gate on the manifest, rule the policy,
 * then build the served composition. `Layer.unwrap` is what lets the
 * two runtime readings — a generated document and a store's config —
 * arrive as ordinary layer construction, so the composition is still
 * provided once, at the command boundary, and never inside a program.
 * The same idiom `layerStoreAt` is written with.
 *
 * A refusal here is the invocation's refusal: nothing is served by a
 * host that cannot prove it serves the emitted table.
 */
export const layerServe = (policy: ServePolicy) =>
  Layer.unwrap(Effect.gen(function* () {
    yield* gateOnManifest
    const limits = yield* applyServePolicy(policy)
    yield* Effect.logInfo("serving").pipe(
      Effect.annotateLogs({
        transport: "stdio",
        server: serverIdentity.name,
        version: serverIdentity.version,
        // Announced so a reader knows what silence means: a gap wider
        // than this in the heartbeat stream is the host stalled.
        heartbeatMs: Duration.toMillis(heartbeatInterval),
      }),
    )
    return layerServeStdio(limits)
  }))

/**
 * Serve until the client closes the pipe. The transport interrupts
 * this fiber when stdin ends, which is how a host that launched this
 * process as a child shuts it down — so the wait is `Effect.never` and
 * the exit is the transport's to decide.
 */
export const serveUntilClosed: Effect.Effect<never, never, McpServer.McpServer> = Effect
  .never

/** The policy a store without one is served under: the same defaults
 * `cas init` writes, so a store predating the config reads the same as
 * one initialized today. */
export const policyOrDefault = (
  policy: ServePolicy | undefined,
): ServePolicy => policy ?? defaultServePolicy
