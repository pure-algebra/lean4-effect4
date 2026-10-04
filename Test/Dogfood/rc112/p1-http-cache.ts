/**
 * Program 1 (seat PROGRAMS, 2026-09-30): an HTTP call with a typed error, a timeout and a
 * retry schedule, whose result is cached per key. Idiomatic Effect rc.112.
 *
 * rc.112 lines relied on (vendor/effect-4.0.0-rc.112/src/):
 *   Data.TaggedError            Data.ts:1111
 *   Effect.tryPromise           Effect.ts:1406-1410; internal/effect.ts:1062-1090 (callbackOptions
 *                               with an AbortController when `try` takes the signal, :1102-1141;
 *                               the abort runs in asyncFinalizer on interruption, :1131-1159)
 *   Effect.timeout              Effect.ts:8293; internal/effect.ts:3707-3727 = timeoutOrElse
 *                               :3677-3704 = raceFirst(self, sleep(d) *> fail(TimeoutError));
 *                               raceFirst = raceAllFirst, first EXIT wins, :1535-1580, :1623-1660
 *   Effect.retry                Effect.ts:7192; Retry.Options Effect.ts:7097-7140 (schedule, while);
 *                               internal/schedule.ts:131-176 -> retryOrElse :51-80 (catch, step, loop)
 *   Schedule.exponential        Schedule.ts:1090-1099 (baseMillis * Math.pow(factor, attempt - 1))
 *   Schedule.upTo               Schedule.ts:1702 (times)
 *   Schedule step and sleep     Schedule.ts:377-411 toStepWithMetadata (reads the clock, steps, sleeps)
 *   Cache.make / Cache.get      Cache.ts:288-309 -> makeWith :190-215 (keeps `lookup` and the
 *                               creation context); Cache.ts:420 get (concurrent misses share one lookup)
 *   Effect.gen                  Effect.ts:1947
 */
import { Cache, Data, Effect, Schedule } from "effect"

/** A structured typed error: a status and the URL. */
export class HttpError extends Data.TaggedError("HttpError")<{
  readonly status: number
  readonly url: string
}> {}

/** The network failed before any status: the rejection reason is kept as data. */
export class NetworkError extends Data.TaggedError("NetworkError")<{
  readonly reason: string
}> {}

/** The decoded body: a record. */
export interface Quote {
  readonly symbol: string
  readonly price: number
}

const base = "https://api.example.com/quotes/"

/** One attempt: fetch (aborted on interruption through the signal), check the status, read the body. */
const fetchOnce = (symbol: string) =>
  Effect.tryPromise({
    try: (signal) => fetch(base + symbol, { signal }),
    catch: (cause) => new NetworkError({ reason: String(cause) })
  }).pipe(
    Effect.flatMap((response): Effect.Effect<Quote, HttpError | NetworkError> =>
      response.ok
        ? Effect.tryPromise({
          try: () => response.json() as Promise<Quote>,
          catch: (cause) => new NetworkError({ reason: String(cause) })
        })
        : Effect.fail(new HttpError({ status: response.status, url: response.url }))
    )
  )

/** The call as a service would expose it: each attempt bounded by a timeout, retried on network
 * failures, timeouts and 5xx answers, with exponential backoff, at most three retries. */
export const fetchQuote = (symbol: string) =>
  fetchOnce(symbol).pipe(
    Effect.timeout("2 seconds"),
    Effect.retry({
      schedule: Schedule.exponential("100 millis").pipe(Schedule.upTo({ times: 3 })),
      while: (error) => error._tag !== "HttpError" || error.status >= 500
    })
  )

/** The cached form: one lookup per symbol, kept for a minute; failures are cached too
 * (Cache.ts:420-430: the cache stores the lookup's Exit). */
export const program = Effect.gen(function*() {
  const quotes = yield* Cache.make({ capacity: 100, timeToLive: "1 minute", lookup: fetchQuote })
  const first = yield* Cache.get(quotes, "EFX")
  const again = yield* Cache.get(quotes, "EFX") // served from the cache, no second request
  return first.price + again.price
}).pipe(
  Effect.catchTag("HttpError", (e) => Effect.succeed(-e.status))
)

/** The checked types, pinned: the error channel is the union of the two tagged errors and the
 * timeout's `Cause.TimeoutError`, less what `catchTag` removed. */
import type { Cause } from "effect"
export const pinFetch: Effect.Effect<Quote, HttpError | NetworkError | Cause.TimeoutError> = fetchQuote("EFX")
export const pinProgram: Effect.Effect<number, NetworkError | Cause.TimeoutError> = program
