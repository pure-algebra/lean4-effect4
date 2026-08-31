// M1 bootstrap check: the pinned effect version resolves and its runtime
// executes under the Effect-native harness. Sampled evidence only; never a
// claim about semantics.
import { expect, it } from "@effect/vitest"
import { Effect } from "effect"

it.effect("pinned effect@4.0.0-rc.111 resolves and runs", () =>
  Effect.gen(function* () {
    const n = yield* Effect.succeed(1)
    expect(n).toBe(1)
  }))
