// The mask's printed form, as the printer would write it, for the type oracle (2026-10-05).
// Checked by tsgo 7 against effect@4.0.0-rc.112 and against effect@4.0.1; not run.
import { Deferred, Effect } from "effect"

// `uninterruptibleMask (restore => restore (await d))`, as nested calls.
export const maskedCalls = (d: Deferred.Deferred<number>): Effect.Effect<number> =>
  Effect.flatMap(
    Effect.uninterruptibleMask((a0) => Effect.succeed(a0)),
    (a0) => Effect.uninterruptible(Deferred.await(d).pipe(a0))
  )

// The same in a generator, as the printer's `gen` row writes a bound statement.
export const maskedGen = (d: Deferred.Deferred<number>): Effect.Effect<number> =>
  Effect.gen(function*() {
    const a0 = yield* Effect.uninterruptibleMask((a0) => Effect.succeed(a0))
    return yield* Effect.uninterruptible(Deferred.await(d).pipe(a0))
  })

// Nested masks: the outer saved value used inside the inner mask, at two answer types.
export const nested = (d: Deferred.Deferred<number>, e: Deferred.Deferred<string>): Effect.Effect<string> =>
  Effect.flatMap(
    Effect.uninterruptibleMask((a0) => Effect.succeed(a0)),
    (a0) =>
      Effect.uninterruptible(
        Effect.flatMap(
          Effect.uninterruptibleMask((a1) => Effect.succeed(a1)),
          (a1) =>
            Effect.uninterruptible(
              Effect.flatMap(Deferred.await(d).pipe(a0), (_a2) => Deferred.await(e).pipe(a1))
            )
        )
      )
  )

// A typed failure passes through a restore site unchanged.
export const failing = (d: Deferred.Deferred<number, "boom">): Effect.Effect<number, "boom"> =>
  Effect.flatMap(
    Effect.uninterruptibleMask((a0) => Effect.succeed(a0)),
    (a0) => Effect.uninterruptible(Deferred.await(d).pipe(a0))
  )

// The red control: a saved value is not a Boolean. This line must be the file's only error.
export const red = Effect.flatMap(
  Effect.uninterruptibleMask((a0) => Effect.succeed(a0)),
  (a0) => Effect.succeed<boolean>(a0)
)
