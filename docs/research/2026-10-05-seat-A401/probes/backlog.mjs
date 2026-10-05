// Seat A401 (2026-10-05). The upstream backlog's two rows, U-01 and U-02, on one Effect build.
// Finite host runs, not proofs.
//
// Run: EFFECT_DIR=<an effect package directory> bun backlog.mjs
// The package directory holds package.json and dist/index.js. The build is loaded by directory:
// the bare name `effect` would load another version from bun's cache.
//
// U-01 rows repeat `docs/research/2026-09-21-foundations-fr08-evidence/VendorEscapeProbe.ts`
// (`quiet`, `poison`) and add four rows around it. U-02 rows repeat
// `docs/research/2026-10-01-landing/seat-D4/VendorScopeCloseProbe.ts` (`zero`, `inline`, `mapOne`,
// `two`, `loneDie`) and add three rows around it.
import { readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR
const version = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const { Deferred, Effect, Exit, Fiber, Scope } = await import(`${dir}/dist/index.js`)

const show = (exit) => ({
  tag: exit._tag,
  ...(Exit.isSuccess(exit)
    ? { value: exit.value === undefined ? "undefined" : exit.value }
    : { cause: String(exit.cause) })
})
const run = (program) => Effect.runPromise(Effect.exit(program)).then(show)

// ---------------------------------------------------------------------------------------------
// U-01. A child fiber waits on a latch inside a masked region. The parent records an interrupt
// on it while it is masked, then opens the latch. The masked region then fails, dies or succeeds.
// ---------------------------------------------------------------------------------------------
const u01 = (poison, body) => {
  const notes = []
  return Effect.gen(function*() {
    const latch = yield* Deferred.make()
    const child = yield* Effect.forkChild(body(latch, notes))
    yield* Effect.yieldNow
    if (poison) child.interruptUnsafe()
    yield* Deferred.succeed(latch, undefined)
    return yield* Effect.exit(Fiber.join(child))
  }).pipe(Effect.runPromise).then((exit) => (notes.length > 0 ? { ...show(exit), notes } : show(exit)))
}

const masked = (latch, after) => Effect.uninterruptible(Effect.andThen(Deferred.await(latch), after))
// The row's reproduction: a catch on an Effect<number, never> fiber.
const caught = (latch) => Effect.catchCause(masked(latch, Effect.fail(42)), () => Effect.succeed(0))
// No recovery handler above the masked region.
const bare = (latch) => masked(latch, Effect.fail(42))
// The masked region dies: a defect is not a typed failure.
const caughtDie = (latch) => Effect.catchCause(masked(latch, Effect.die("boom")), () => Effect.succeed(0))
// An inner handler in an interruptible region, and an outer handler in a masked region. Each
// handler notes the cause it was handed. The fiber's own exit is the interrupt in every case,
// because the last mask to lift applies the recorded interrupt.
const outerHandler = (latch, notes) =>
  Effect.uninterruptible(
    Effect.catchCause(
      Effect.interruptible(
        Effect.catchCause(masked(latch, Effect.fail(42)), (cause) =>
          Effect.sync(() => {
            notes.push(`inner handler saw ${String(cause)}`)
          }))
      ),
      (cause) =>
        Effect.sync(() => {
          notes.push(`outer handler saw ${String(cause)}`)
        })
    )
  )
// A finalizer between the failure and the fiber's exit notes the exit it was handed.
const finalizerSees = (latch, notes) =>
  Effect.onExit(caught(latch), (exit) =>
    Effect.sync(() => {
      notes.push(`finalizer saw ${Exit.isSuccess(exit) ? `success ${exit.value}` : String(exit.cause)}`)
    }))

// ---------------------------------------------------------------------------------------------
// U-02. `Scope.close` is declared Effect<void>. What does it answer?
// ---------------------------------------------------------------------------------------------
const release = (n) => Effect.acquireRelease(Effect.succeed(1), () => Effect.succeed(n))

const u02 = {
  zero: Effect.gen(function*() {
    const scope = yield* Scope.make()
    return yield* Scope.close(scope, Exit.void)
  }),
  inline: Effect.gen(function*() {
    const scope = yield* Scope.make()
    yield* Scope.provide(release(5), scope)
    return yield* Scope.close(scope, Exit.void)
  }),
  mapOne: Effect.gen(function*() {
    const scope = yield* Scope.make()
    yield* Scope.provide(release(5), scope)
    const child = yield* Scope.fork(scope)
    yield* Scope.close(child, Exit.void)
    return yield* Scope.close(scope, Exit.void)
  }),
  two: Effect.gen(function*() {
    const scope = yield* Scope.make()
    yield* Scope.provide(release(5), scope)
    yield* Scope.provide(release(6), scope)
    return yield* Scope.close(scope, Exit.void)
  }),
  loneDie: Effect.gen(function*() {
    const scope = yield* Scope.make()
    yield* Scope.provide(Effect.acquireRelease(Effect.succeed(1), () => Effect.die("boom")), scope)
    return yield* Scope.close(scope, Exit.void)
  }),
  // Added: a forked child scope that holds one finalizer of its own.
  forkedChildOne: Effect.gen(function*() {
    const parent = yield* Scope.make()
    const child = yield* Scope.fork(parent)
    yield* Scope.provide(release(7), child)
    return yield* Scope.close(child, Exit.void)
  }),
  // Added: the state of a parent after its only child closed.
  parentAfterChildClose: Effect.gen(function*() {
    const parent = yield* Scope.make()
    const child = yield* Scope.fork(parent)
    const before = parent.state._tag
    yield* Scope.close(child, Exit.void)
    return `${before} -> ${parent.state._tag}`
  }),
  // Added: a fiber is interrupted while the lone finalizer of the scope it closes is waiting.
  closeInterruptedMidFinalizer: Effect.gen(function*() {
    const scope = yield* Scope.make()
    const log = []
    yield* Scope.addFinalizer(
      scope,
      Effect.gen(function*() {
        log.push("finalizer started")
        yield* Effect.yieldNow
        yield* Effect.yieldNow
        log.push("finalizer finished")
      })
    )
    const closer = yield* Effect.forkChild(Scope.close(scope, Exit.void))
    yield* Effect.yieldNow
    const exit = yield* Fiber.interrupt(closer).pipe(Effect.andThen(Fiber.await(closer)))
    return { log: log.join(", "), closer: exit._tag }
  })
}

const out = { effect: version, u01: {}, u02: {} }
out.u01.quiet = await u01(false, caught)
out.u01.poison = await u01(true, caught)
out.u01.poisonNoHandler = await u01(true, bare)
out.u01.poisonDie = await u01(true, caughtDie)
out.u01.quietOuterHandler = await u01(false, outerHandler)
out.u01.poisonOuterHandler = await u01(true, outerHandler)
out.u01.poisonFinalizerSees = await u01(true, finalizerSees)
for (const [name, program] of Object.entries(u02)) out.u02[name] = await run(program)
console.log(JSON.stringify(out, null, 1))
