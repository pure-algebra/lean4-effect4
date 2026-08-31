/**
 * The host's own vital signs — BS-1, "the host cannot stall silently".
 *
 * ## The constraint that shapes this module
 *
 * A blocked event loop cannot report that it is blocked. `bun:sqlite`
 * is synchronous, so a busy wait on the write lock stops every fiber,
 * every timer, and every log flush in the process at once. Any metric,
 * span, or log line written from inside such a process is silent
 * exactly when it is most wanted.
 *
 * So the detector cannot be a line that says "stalled". It has to be a
 * line whose ABSENCE says it: a heartbeat on a fixed period, whose gap
 * is measured and reported by the beat that follows it. `lateMs` on a
 * heartbeat line IS the stall duration, and a missing line is a stall
 * still in progress. Nothing else in the host can see the hazard,
 * because everything else in the host is stopped by it.
 *
 * ## The four metrics
 *
 * Effect-native at the pin, and no layer is required to hold them:
 * `Metric.MetricRegistry` is a `Context.Reference` carrying a default
 * `Map`, so a metric updated under no explicit registry still lands
 * somewhere `Metric.snapshot` can read it. (Its own documented gotcha:
 * that default `Map` is SHARED by every context that does not override
 * it, which is why a test that asserts on counts provides a fresh one.)
 *
 * - `cas.host.inflight` — gauge. The number of store-touching calls
 *   past the admission gate. The one number that says whether the
 *   ~46 KB-per-request growth the audit measured is running away.
 * - `cas.host.calls` — counter, attributed by `tool` and `outcome`.
 * - `cas.store.sql_wait` — timer around the SQL path. The head-of-line
 *   stall's own measurement: a read that queued behind a writer shows
 *   up here as milliseconds, whatever the reason it queued.
 * - `cas.host.refused` — counter, attributed by `clause`. Every typed
 *   refusal the host issues is counted under the clause it carried.
 *
 * The pin's mutator is `Metric.update(metric, value)`. There is no
 * `Metric.increment` and no callable-metric wrapper, so a counter is
 * incremented by updating it with `1`.
 *
 * ## Why this module sits under `bin/mcp/`
 *
 * These are the HOST's numbers, and the host is what BS-1 is about.
 * `bin/cli/store.ts` imports `sqlWait` from here rather than the other
 * way round, which keeps the dependency one-directional: this module
 * imports nothing from the CLI and never will.
 */
import { Clock, Duration, Effect, Layer, Metric } from "effect"

/* ── the four metrics ────────────────────────────────────────────── */

/** Store-touching calls currently past the admission gate. */
export const inflight = Metric.gauge("cas.host.inflight", {
  description: "store-touching MCP calls currently in flight",
})

/** Every tool call, by tool and by how it ended. */
export const calls = Metric.counter("cas.host.calls", {
  description: "MCP tool calls, by tool and outcome",
  incremental: true,
})

/** Bucket boundaries for the SQL path, in milliseconds, and FINITE on
 * purpose — the same reason `cas.daemon.request` carries its own set.
 * `Metric.timer`'s default boundaries END in `Infinity`, and the
 * Prometheus exposition renders every boundary as a bucket AND then
 * appends its own `le="+Inf"` row, so the default publishes a
 * duplicate overflow bucket labelled `le="Infinity"` — not a number
 * Prometheus parses. Anything past the top lands in the histogram's
 * overflow slot, which the exporter reports as `+Inf`.
 *
 * The ladder is the shape this path actually has: sub-millisecond
 * when the connection is free, seconds when the head-of-line stall
 * the audit measured is in progress. */
export const sqlWaitBoundaries: ReadonlyArray<number> = [
  0.5,
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
  5000,
]

/** How long the SQL path took, wait included. */
export const sqlWait = Metric.timer("cas.store.sql_wait", {
  description: "time spent in the SQL path, including the wait for a connection",
  boundaries: sqlWaitBoundaries,
})

/** Typed refusals, by the clause they carried. */
export const refused = Metric.counter("cas.host.refused", {
  description: "typed refusals issued by the host, by clause",
  incremental: true,
})

/** Count one call's outcome. The attributes are the two things a
 * reader of the log already has: which tool, and how it ended. */
export const countCall = (
  tool: string,
  outcome: "ok" | "refused" | "failed",
): Effect.Effect<void> =>
  Metric.update(Metric.withAttributes(calls, { tool, outcome }), 1)

/** Count one refusal under its own clause — the same clause the
 * `Refused` reply carries, so the metric and the wire agree. */
export const countRefusal = (clause: string): Effect.Effect<void> =>
  Metric.update(Metric.withAttributes(refused, { clause }), 1)

/** Time an effect into `cas.store.sql_wait`. The duration is recorded
 * whether the effect succeeded or failed: a refusal that took four
 * seconds to arrive is exactly the observation this metric exists for,
 * so `Effect.onExit` is what records it rather than a success-only
 * wrapper. */
export const timeSql = <A, E, R>(self: Effect.Effect<A, E, R>): Effect.Effect<A, E, R> =>
  Clock.currentTimeMillis.pipe(
    Effect.flatMap((started) =>
      self.pipe(
        Effect.onExit(() =>
          Clock.currentTimeMillis.pipe(
            Effect.flatMap((ended) =>
              Metric.update(sqlWait, Duration.millis(ended - started))
            ),
          )
        ),
      )
    ),
  )

/* ── the heartbeat ───────────────────────────────────────────────── */

/** The beat period. Two seconds: short enough that the 5-second
 * `busy_timeout` ceiling on a SQLite stall shows up as at least two
 * late beats, long enough that a quiet host's log stays readable. */
export const heartbeatInterval: Duration.Duration = Duration.seconds(2)

const intervalMillis = Duration.toMillis(heartbeatInterval)

/** One snapshot rendered as one logfmt-safe field. Counters and gauges
 * report their number; a histogram reports the shape a reader of a
 * stall actually wants — how many observations, and the worst one. */
export const renderSnapshots = (
  snapshots: ReadonlyArray<Metric.Metric.Snapshot>,
): string =>
  snapshots
    .map((snapshot) => {
      const attributes = snapshot.attributes === undefined
        ? ""
        : `{${
          Object.entries(snapshot.attributes)
            .map(([key, value]) => `${key}=${String(value)}`)
            .join(",")
        }}`
      const state = snapshot.type === "Counter" || snapshot.type === "Gauge"
        ? String(snapshot.type === "Counter" ? snapshot.state.count : snapshot.state.value)
        : snapshot.type === "Histogram"
        ? `count=${snapshot.state.count},max=${snapshot.state.max}`
        : ""
      return `${snapshot.id}${attributes}=${state}`
    })
    .join(" ")

/**
 * The beat. Sleeps the interval, then reports how long the sleep
 * ACTUALLY took — `lateMs` is the excess over the interval, and it is
 * the stall detector's whole output. A loop blocked for four seconds
 * cannot log during the block; it logs `lateMs=4000` the moment it is
 * released, and a reader watching the stream sees a six-second silence
 * followed by that number.
 *
 * Runs at INFO so the default log level carries it: a heartbeat nobody
 * sees detects nothing.
 */
export const heartbeat: Effect.Effect<never> = Effect.suspend(() => {
  // The previous beat's wall clock, held in the fiber's own closure.
  // It is the only state the detector has, and it is the whole
  // detector: everything else in the process is stopped when the thing
  // being detected happens.
  let previous = 0
  const beat = Effect.sleep(heartbeatInterval).pipe(
    Effect.andThen(Clock.currentTimeMillis),
    Effect.flatMap((now) => {
      const elapsed = now - previous
      previous = now
      return Metric.snapshot.pipe(
        Effect.flatMap((snapshots) =>
          Effect.logInfo("heartbeat").pipe(
            Effect.annotateLogs({
              elapsedMs: elapsed,
              // Zero on a healthy host. Anything else is time the
              // process spent unable to run this fiber.
              lateMs: Math.max(0, elapsed - intervalMillis),
              metrics: renderSnapshots(snapshots),
            }),
          )
        ),
      )
    }),
  )
  return Clock.currentTimeMillis.pipe(
    Effect.flatMap((started) => {
      previous = started
      return Effect.forever(beat)
    }),
  )
})

/**
 * The heartbeat as a layer: forked into the layer's own scope, so it
 * lives exactly as long as the host does and is interrupted with it.
 * `Layer.effectDiscard` because it provides nothing — it is a fiber the
 * composition starts, not a service anything asks for.
 */
export const layerHeartbeat: Layer.Layer<never> = Layer.effectDiscard(
  // The gauge is set to zero before the first beat so it is REGISTERED
  // from the start: `Metric.snapshot` reports only metrics that have
  // been touched, and a heartbeat whose metrics field is empty until
  // the first call reads as a host that is not measuring anything.
  Metric.update(inflight, 0).pipe(Effect.andThen(Effect.forkScoped(heartbeat))),
)
