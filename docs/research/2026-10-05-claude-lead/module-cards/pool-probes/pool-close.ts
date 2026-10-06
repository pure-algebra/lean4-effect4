// Does closing a pool's scope wait for a borrowed item? (2026-10-06) One finite host run on each
// build, not a proof. It runs on Effect 3 and on Effect 4.
//
// Run: EFFECT_DIR=<an effect package directory> bun run pool-close.ts
// Size 1. H borrows the item and holds it. The pool's scope is then closed by another fiber.
// The probe records whether the close has finished while H still holds, and the order of the
// resource's finalizer and H's return.
import { existsSync, readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const entry = existsSync(`${dir}/dist/index.js`) ? `${dir}/dist/index.js` : `${dir}/dist/esm/index.js`
const { Effect, Deferred, Pool, Scope, Exit } = await import(entry)

const v4 = typeof Effect.forkChild === "function"
const fork = v4 ? Effect.forkChild : Effect.fork
const yieldNow = v4 ? Effect.yieldNow : Effect.yieldNow()
const settle = Effect.gen(function*() {
  for (let i = 0; i < 40; i++) yield* yieldNow
})

const probe = Effect.gen(function*() {
  const log: Array<string> = []
  const acquire = Effect.acquireRelease(
    Effect.sync(() => { log.push("acquire 1"); return 1 }),
    () => Effect.sync(() => { log.push("finalize 1") })
  )
  const scope = yield* Scope.make()
  const pool = yield* Effect.provideService(Pool.make({ acquire, size: 1 }), Scope.Scope, scope)
  yield* settle
  const gate = yield* Deferred.make()
  yield* fork(Effect.scoped(Effect.gen(function*() {
    const r = yield* Pool.get(pool)
    log.push(`H got ${r}`)
    yield* Deferred.await(gate)
    log.push(`H returns ${r}`)
  })))
  yield* settle
  let closed = false
  yield* fork(Effect.gen(function*() {
    log.push("the pool's scope starts to close")
    yield* Scope.close(scope, Exit.void)
    closed = true
    log.push("the pool's scope is closed")
  }))
  yield* settle
  const closedWhileHHolds = closed
  yield* Deferred.succeed(gate, undefined)
  yield* settle
  return { closedWhileHHolds, closedAfterTheReturn: closed, log }
})

const out = { effect: version, runtime: `bun ${Bun.version}`, ...(await Effect.runPromise(probe)) }
console.log(JSON.stringify(out, null, 1))
