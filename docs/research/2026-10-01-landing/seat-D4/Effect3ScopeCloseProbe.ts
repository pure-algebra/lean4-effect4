// The comparison run for U-02 on Effect 3.21.2 (a local install, not pinned in this repository:
// /Users/pooks/Dev/effect-jetstream/node_modules/effect, read at dist/esm/internal/fiberRuntime.js
// :1885-1904, whose `close` maps every finalizer count above zero through `exitAsVoid`).
// Rows as in VendorScopeCloseProbe.ts. Run: bun docs/research/2026-10-01-landing/seat-D4/Effect3ScopeCloseProbe.ts
import { Effect, Exit, Scope } from "/Users/pooks/Dev/effect-jetstream/node_modules/effect/dist/esm/index.js"

const release = (n: number) => Effect.acquireRelease(Effect.succeed(1), () => Effect.succeed(n))

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
  yield* Scope.extend(release(5), scope)
  return yield* Scope.close(scope, Exit.void)
}))
await record("two", Effect.gen(function*() {
  const scope = yield* Scope.make()
  yield* Scope.extend(release(5), scope)
  yield* Scope.extend(release(6), scope)
  return yield* Scope.close(scope, Exit.void)
}))

console.log(JSON.stringify({ scope: "Effect 3.21.2 (local install, comparison only)", rows }, null, 2))
