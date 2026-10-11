/** DI-09 finite host controls for the rc.112 catchIf clause before native lowering.
 * Source: vendor/effect-4.0.0-rc.112/src/internal/effect.ts:2803-2810.
 * Tested: first-Fail selection, whole-cause miss/hit, and completed state retention.
 * These controls do not establish the native compiler relation. */
import { expect, test } from "bun:test"
import { Cause, Effect, Exit, Ref } from "effect"

const mixed = Cause.fromReasons([
  Cause.makeInterruptReason(1), Cause.makeFailReason("first"),
  Cause.makeDieReason("defect"), Cause.makeFailReason("second"),
])

test("catchIf selects only the first Fail and a miss retains the entire cause", async () => {
  const seen: string[] = []
  const exit = await Effect.runPromiseExit(Effect.catchIf(
    Effect.failCause(mixed),
    error => { seen.push(error); return error === "second" },
    () => Effect.succeed(7),
  ))
  expect(seen).toEqual(["first"])
  expect(exit).toEqual(Exit.failCause(mixed))
})

test("catchIf hit replaces a mixed cause including its defect and interruption", async () => {
  const exit = await Effect.runPromiseExit(Effect.catchIf(
    Effect.failCause(mixed), error => error === "first", () => Effect.succeed(7),
  ))
  expect(exit).toEqual(Exit.succeed(7))
})

test("no Fail leaves the cause intact and invokes neither predicate nor handler", async () => {
  const cause = Cause.combine(Cause.die("defect"), Cause.interrupt(1))
  let called = 0
  const exit = await Effect.runPromiseExit(Effect.catchIf(
    Effect.failCause(cause),
    () => { called++; return true },
    () => { called++; return Effect.succeed(7) },
  ))
  expect(exit).toEqual(Exit.failCause(cause))
  expect(called).toBe(0)
})

test("body state survives both catchIf hit and miss", async () => {
  for (const hit of [true, false]) {
    const observed = await Effect.runPromise(Effect.gen(function* () {
      const ref = yield* Ref.make(0)
      const body = Effect.andThen(Ref.set(ref, 9), Effect.fail("first"))
      const exit = yield* Effect.exit(Effect.catchIf(body, () => hit, () => Ref.get(ref)))
      return { exit, value: yield* Ref.get(ref) }
    }))
    expect(observed.value).toBe(9)
    expect(observed.exit).toEqual(hit ? Exit.succeed(9) : Exit.fail("first"))
  }
})
