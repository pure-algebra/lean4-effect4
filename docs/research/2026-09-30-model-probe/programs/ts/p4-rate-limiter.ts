/**
 * Program 4 (seat PROGRAMS, 2026-09-30): dogfood 1, the fixed-window rate limiter of
 * docs/research/2026-09-15-dogfood-1-receipt.md §1 (limit 3 per 1000 ms window, a refill daemon,
 * five concurrent requests, explicit shutdown), written as an rc.112 user would write it.
 *
 * Two departures from the dogfood's idiomatic file (2026-09-15-dogfood-1-evidence/
 * idiomatic_rate_limiter.ts), both on purpose:
 *   - `Effect.forkDaemon` (that file's line 9) is not an rc.112 export (grep of the pinned src finds
 *     nothing); rc.112 spells it `Effect.forkDetach` (Effect.ts:17168).
 *   - The state is one record in one Ref, admitted by `Ref.modify` in one atomic step; the dogfood
 *     read then updated three Refs, which races under a yield (its `pYielding` answers [5, 0]).
 *
 * rc.112 lines relied on (vendor/effect-4.0.0-rc.112/src/):
 *   Ref.make / get / set / modify   Ref.ts:173, :200, :236, :797
 *   Effect.forkDetach               Effect.ts:17168 (a child that outlives its parent)
 *   Effect.forever                  Effect.ts:14480
 *   Effect.sleep                    Effect.ts:8696; internal/effect.ts:6114-6116 (0 ms is a yield, :6055)
 *   Effect.all (concurrency)        Effect.ts:494; internal/effect.ts:4383
 *   Fiber.interrupt                 Fiber.ts:354
 */
import { Effect, Fiber, Ref } from "effect"

/** The limiter's state: a record. */
interface Window {
  readonly used: number
  readonly admitted: number
  readonly rejected: number
}

/** Admit or reject one request in one atomic step; answer the decision. */
const request = (limit: number, state: Ref.Ref<Window>) =>
  Ref.modify(state, (w): [boolean, Window] =>
    w.used < limit
      ? [true, { ...w, used: w.used + 1, admitted: w.admitted + 1 }]
      : [false, { ...w, rejected: w.rejected + 1 }]
  )

/** The refill daemon: every window, reset the count. */
const refill = (windowMillis: number, state: Ref.Ref<Window>) =>
  Effect.forever(
    Effect.sleep(windowMillis).pipe(
      Effect.andThen(Ref.update(state, (w) => ({ ...w, used: 0 })))
    )
  )

export const program = Effect.gen(function*() {
  const state = yield* Ref.make<Window>({ used: 0, admitted: 0, rejected: 0 })
  const daemon = yield* Effect.forkDetach(refill(1000, state))
  const decisions = yield* Effect.all(
    [request(3, state), request(3, state), request(3, state), request(3, state), request(3, state)],
    { concurrency: "unbounded" }
  )
  yield* Fiber.interrupt(daemon) // shutdown: the daemon ends interrupted
  const w = yield* Ref.get(state)
  return [w.admitted, w.rejected, decisions.filter((d) => d).length] as const
})

/** The checked type, pinned. */
export const pinProgram: Effect.Effect<readonly [number, number, number]> = program
