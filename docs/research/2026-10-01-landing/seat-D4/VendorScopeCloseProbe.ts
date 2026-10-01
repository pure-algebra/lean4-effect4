// End-to-end run of the pinned rc.112 source (decisions row 151, upstream backlog U-02):
// `Scope.close` is declared `Effect<void>` (Scope.ts:567) but answers the value of a scope's
// lone finalizer (internal/effect.ts:3775-3776 passing on scopeCloseUnsafe's
// :3788-3789 inline slot and :3794-3795 one-entry map). Rows:
//   zero      no finalizer                                    -> void
//   inline    one acquireRelease release answering 5         -> 5   (:3788-3789)
//   mapOne    the release, then a child scope forked and closed,
//             leaving a one-entry map on the parent           -> 5   (:3794-3795)
//   two       two releases answering 5 and 6                  -> void (the walk, exitAsVoidAll)
//   lone die  one release that dies                           -> the defect passes through
// Run from the repository root: bun docs/research/2026-10-01-landing/seat-D4/VendorScopeCloseProbe.ts
import * as Effect from "../../../../vendor/effect-4.0.0-rc.112/src/Effect.ts"
import * as Exit from "../../../../vendor/effect-4.0.0-rc.112/src/Exit.ts"
import * as Scope from "../../../../vendor/effect-4.0.0-rc.112/src/Scope.ts"

const release = (n: number) =>
  Effect.acquireRelease(Effect.succeed(1), () => Effect.succeed(n))

const rows: Array<Record<string, unknown>> = []
const record = async (name: string, program: Effect.Effect<unknown, unknown>) => {
  const exit = await Effect.runPromise(Effect.exit(program))
  rows.push({
    name,
    tag: exit._tag,
    value: Exit.isSuccess(exit) ? (exit.value === undefined ? "undefined" : exit.value) : undefined,
    cause: Exit.isFailure(exit) ? String(exit.cause) : undefined
  })
}

await record("zero", Effect.gen(function*() {
  const scope = yield* Scope.make()
  return yield* Scope.close(scope, Exit.void)
}))

await record("inline", Effect.gen(function*() {
  const scope = yield* Scope.make()
  yield* Scope.provide(release(5), scope)
  return yield* Scope.close(scope, Exit.void)
}))

await record("mapOne", Effect.gen(function*() {
  const scope = yield* Scope.make()
  yield* Scope.provide(release(5), scope)
  const child = yield* Scope.fork(scope)
  yield* Scope.close(child, Exit.void)
  return yield* Scope.close(scope, Exit.void)
}))

await record("two", Effect.gen(function*() {
  const scope = yield* Scope.make()
  yield* Scope.provide(release(5), scope)
  yield* Scope.provide(release(6), scope)
  return yield* Scope.close(scope, Exit.void)
}))

await record("loneDie", Effect.gen(function*() {
  const scope = yield* Scope.make()
  yield* Scope.provide(Effect.acquireRelease(Effect.succeed(1), () => Effect.die("boom")), scope)
  return yield* Scope.close(scope, Exit.void)
}))

console.log(JSON.stringify({
  scope: "pinned rc.112 source run end to end with bun; Scope.close is declared Effect<void> (Scope.ts:567)",
  rows
}, null, 2))
