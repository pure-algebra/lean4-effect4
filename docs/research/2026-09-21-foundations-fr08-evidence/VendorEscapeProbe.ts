// End-to-end run of the pinned rc.112 source: a catch on an Effect<number, never>
// fiber is skipped when an interrupt was recorded during a masked region and the masked
// region then fails. Two rows: quiet (no interrupt) and poisoned (interrupt while masked).
import * as Effect from "../../../vendor/effect-4.0.0-rc.112/src/Effect.ts"
import * as Fiber from "../../../vendor/effect-4.0.0-rc.112/src/Fiber.ts"
import * as Deferred from "../../../vendor/effect-4.0.0-rc.112/src/Deferred.ts"
import * as Exit from "../../../vendor/effect-4.0.0-rc.112/src/Exit.ts"

const scenario = (poison: boolean) =>
  Effect.gen(function*() {
    const latch = yield* Deferred.make<void>()
    // child : Fiber<number, never>
    const child = yield* Effect.forkChild(
      Effect.catchCause(
        Effect.uninterruptible(Effect.andThen(Deferred.await(latch), Effect.fail(42))),
        () => Effect.succeed(0)
      )
    )
    yield* Effect.yieldNow
    if (poison) child.interruptUnsafe()
    yield* Deferred.succeed(latch, undefined)
    return yield* Effect.exit(Fiber.join(child))
  })

const rows: Array<Record<string, unknown>> = []
for (const poison of [false, true]) {
  const exit = await Effect.runPromise(scenario(poison))
  rows.push({
    poison,
    tag: exit._tag,
    value: Exit.isSuccess(exit) ? exit.value : undefined,
    cause: Exit.isFailure(exit) ? String(exit.cause) : undefined
  })
}
console.log(JSON.stringify({
  scope: "pinned rc.112 source run end to end with bun; the child is typed Fiber<number, never>",
  rows
}, null, 2))
