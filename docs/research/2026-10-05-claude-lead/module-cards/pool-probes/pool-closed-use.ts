// What does a borrow answer at a pool whose scope has closed? (2026-10-06) One finite host run
// on each build, not a proof. It runs on Effect 4.
//
// Run: EFFECT_DIR=<an effect package directory> bun run pool-closed-use.ts
// Size 1. Case A: the pool's scope closes with no borrower, and then a fiber borrows.
// Case B: H holds the item, the scope closes, and then a second fiber borrows while H holds.
// The probe records each late borrower's exit, and whether its body ran.
import { existsSync, readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const entry = existsSync(`${dir}/dist/index.js`) ? `${dir}/dist/index.js` : `${dir}/dist/esm/index.js`
const { Effect, Deferred, Pool, Scope, Exit, Fiber } = await import(entry)

const settle = Effect.gen(function*() {
  for (let i = 0; i < 40; i++) yield* Effect.yieldNow
})

const show = (exit: any): string => {
  try { return JSON.stringify(exit) } catch { return String(exit) }
}

const run = (holder: boolean) => Effect.gen(function*() {
  const log: Array<string> = []
  const acquire = Effect.acquireRelease(
    Effect.sync(() => { log.push("acquire 1"); return 1 }),
    () => Effect.sync(() => { log.push("finalize 1") })
  )
  const scope = yield* Scope.make()
  const pool = yield* Effect.provideService(Pool.make({ acquire, size: 1 }), Scope.Scope, scope)
  yield* settle
  const gate = yield* Deferred.make()
  if (holder) {
    yield* Effect.forkChild(Effect.scoped(Effect.gen(function*() {
      const r = yield* Pool.get(pool)
      log.push(`H got ${r}`)
      yield* Deferred.await(gate)
      log.push(`H returns ${r}`)
    })))
    yield* settle
  }
  yield* Scope.close(scope, Exit.void)
  log.push("the pool's scope is closed")
  let bodyRan = false
  const late = yield* Effect.forkChild(Effect.scoped(Effect.gen(function*() {
    const r = yield* Pool.get(pool)
    bodyRan = true
    log.push(`L got ${r}`)
  })))
  yield* settle
  const lateExit = late.pollUnsafe ? late.pollUnsafe() : undefined
  log.push(lateExit === undefined ? "L has no exit yet" : "L has exited")
  yield* Deferred.succeed(gate, undefined)
  yield* settle
  const exit = yield* Fiber.await(late)
  return { bodyRan, lateExitedBeforeTheReturn: lateExit !== undefined, exit: show(exit), log }
})

const out = {
  effect: version, runtime: `bun ${Bun.version}`,
  noBorrower: await Effect.runPromise(run(false)),
  aBorrowerHolds: await Effect.runPromise(run(true))
}
console.log(JSON.stringify(out, null, 1))
