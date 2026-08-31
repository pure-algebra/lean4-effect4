/**
 * `cas daemon` — the long-lived host, spoken from a shell.
 *
 * One process, one port, both wire planes: cas-http/0 (the profile's
 * data, control, and roots spaces) and MCP over HTTP (`/mcp`), plus
 * `/metrics` for Prometheus. The composition lives in
 * `bin/mcp/http.ts`; this file is the verb — flags, store resolution,
 * and the same provide-once discipline every other verb keeps.
 *
 * Stated non-goals of v0, so the help never over-promises:
 *
 * - NO TLS and NO credentials. The daemon binds loopback by default
 *   and trusts its network position; TLS termination and everything
 *   that belongs behind it (bearer credentials, rate limits,
 *   connection caps) is the adopted front proxy's job — see
 *   library/effects/SERVING.md for the Caddy composition. A store whose
 *   policy sets `anonymousReads: false` is REFUSED at boot, not served
 *   open.
 * - MCP protocol revision 2026-07-28 is not offered (the pin carries
 *   through 2025-11-25), and the Streamable HTTP endpoint implements
 *   no legacy SSE topology and no session resumption — the adapter's
 *   own documented scope.
 *
 * ## Why this verb does not use `layerStoreAt`
 *
 * The boundary layer every read verb shares deliberately narrows the
 * byte plane to `ByteReader` — a verb that only reads must not hold a
 * writer. The daemon serves uploads on both planes, so it is composed
 * from the same pieces one level down: `locateStore`, `readConfig`,
 * and `layerCasAt`, which answers the writer seam too. Same doors,
 * same refusals, one more seam.
 */
import {
  Cause,
  Config,
  Effect,
  Layer,
  Option,
} from "effect"
import { CliError, Command, Flag } from "effect/unstable/cli"
import { Cas } from "../../src/index.ts"
import { layerDaemon } from "../mcp/http.ts"
import { layerStderrLogs, policyOrDefault } from "../mcp/server.ts"
import { casErrorMessage } from "./render.ts"
import { backendOf, layerCasAt, locateStore, readConfig } from "./store.ts"

/**
 * Failures rendered as user errors, exactly as `bin/cli/commands.ts`
 * renders them. Restated here rather than imported because that file
 * belongs to the CLI lane and exports verbs only; the two copies are
 * candidates for one shared home when the lanes next converge.
 */
const userFacing = <A, E, R>(
  program: Effect.Effect<A, E, R>,
): Effect.Effect<A, CliError.UserError, R> =>
  Effect.mapError(program, (error) => {
    const message = Cas.isCasError(error)
      ? casErrorMessage(error)
      : Cause.prettyErrors(Cause.fail(error))
        .map((pretty) => pretty.message)
        .join("\n")
    return new CliError.UserError({ cause: error, userMessage: message })
  })

/** Flag, then `CAS_STORE`, then walk-up discovery — the same
 * resolution order every verb answers to. */
const storeFlag = Flag.string("store").pipe(
  Flag.withFallbackConfig(Config.string("CAS_STORE")),
  Flag.optional,
  Flag.withDescription(
    "the store to use; otherwise CAS_STORE, otherwise every parent is searched for a .cas directory",
  ),
)

/**
 * The daemon over the store this invocation resolves. The policy is
 * the store's own (`config.json`, written by `init`); the flags are
 * this invocation's: where to bind, whether to override the policy's
 * port, where to export OTLP. The store composition is `layerCasAt`
 * over the backend the config declares — the same store, the same
 * seams, whichever transport asks.
 */
/** A comma-separated flag value as its entries, empty for absent. */
const entriesOf = (flag: Option.Option<string>): ReadonlyArray<string> =>
  Option.match(flag, {
    onNone: () => [],
    onSome: (raw) =>
      raw.split(",").map((entry) => entry.trim()).filter((entry) => entry.length > 0),
  })

const layerDaemonAt = (options: {
  readonly store: Option.Option<string>
  readonly host: string
  readonly port: Option.Option<number>
  readonly otlp: Option.Option<string>
  readonly allowOrigin: Option.Option<string>
  readonly allowHost: Option.Option<string>
}) =>
  Layer.unwrap(Effect.gen(function* () {
    const location = yield* locateStore(options.store)
    const config = yield* readConfig(location)
    yield* Effect.logInfo("store opened").pipe(
      Effect.annotateLogs({ store: location.store, origin: location.origin }),
    )
    const policy = policyOrDefault(
      Option.isSome(config) ? config.value.serve : undefined,
    )
    const replicaTarget = Option.isSome(config) && config.value.backup !== undefined
      ? Option.some(config.value.backup.target)
      : Option.none<string>()
    return layerDaemon({
      policy,
      host: options.host,
      port: options.port,
      otlp: options.otlp,
      replicaTarget,
      allowedOrigins: entriesOf(options.allowOrigin),
      allowedHosts: entriesOf(options.allowHost),
    }).pipe(
      Layer.provideMerge(layerCasAt(location.store, backendOf(config))),
    )
  }))

export const daemon = Command.make("daemon", {
  store: storeFlag,
  host: Flag.string("host").pipe(
    Flag.withDefault("127.0.0.1"),
    Flag.withDescription(
      "the address to bind — loopback by default; widen it only behind the TLS proxy (see library/effects/SERVING.md)",
    ),
  ),
  port: Flag.integer("port").pipe(
    Flag.optional,
    Flag.withDescription(
      "override the store policy's port for this invocation (0 asks the OS for an ephemeral port)",
    ),
  ),
  otlp: Flag.string("otlp").pipe(
    Flag.optional,
    Flag.withDescription(
      "export logs, metrics, and traces as OTLP/JSON to this collector base URL",
    ),
  ),
  allowOrigin: Flag.string("allow-origin").pipe(
    Flag.optional,
    Flag.withDescription(
      "comma-separated browser origins allowed to call this port (CORS); by default every Origin-carrying request is refused",
    ),
  ),
  allowHost: Flag.string("allow-host").pipe(
    Flag.optional,
    Flag.withDescription(
      "comma-separated extra Host names to accept (the front proxy's public name); loopback and the bound host are always accepted",
    ),
  ),
}, ({ allowHost, allowOrigin, host, otlp, port, store }) =>
  Effect.never.pipe(
    // One provide, not two: the log layer is fed to the daemon
    // composition rather than chained beneath it, so the whole store
    // is built under the same logger and the two layers share one
    // lifecycle (effect(multipleEffectProvide)).
    Effect.provide(Layer.provideMerge(
      layerDaemonAt({ store, host, port, otlp, allowOrigin, allowHost }),
      layerStderrLogs,
    )),
    userFacing,
  )).pipe(
    // The verb table gets the one line; `daemon --help` gets the rest.
    // Same reason `serve` carries a short form: without it the whole
    // paragraph below is repeated inside `cas --help`'s subcommand
    // listing.
    Command.withShortDescription(
      "serve this store on one port, long-lived — both wire planes, no TLS of its own; see daemon --help",
    ),
    Command.withDescription(
    [
      "serve this store on one port, long-lived: cas-http/0 (data, control, roots), MCP over HTTP at /mcp, Prometheus at /metrics, emitted artifacts at /projections",
      "",
      "logs are logfmt on stderr; a heartbeat line every 2s carries the metric snapshot, and a missing beat is a detected stall",
      "browser requests are refused unless their origin is named with --allow-origin; foreign Host headers are refused (DNS-rebinding posture)",
      "not yet spoken, on purpose: TLS and credentialed reads (front the daemon with the TLS proxy; anonymousReads:false refuses at boot)",
    ].join("\n"),
  ))
