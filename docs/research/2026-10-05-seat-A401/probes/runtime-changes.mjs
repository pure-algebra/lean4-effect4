// Seat A401 (2026-10-05). Suspected changes of behaviour of the run loop, on one Effect build.
// Finite host runs, not proofs. Each row states what the reading of the two sources predicts.
//
// Run: EFFECT_DIR=<an effect package directory> bun runtime-changes.mjs
// The build is loaded by directory; the bare name `effect` would load another version.
import { readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR
const version = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const { Deferred, Effect, Exit, Fiber, Scheduler } = await import(`${dir}/dist/index.js`)

const show = (exit) =>
  Exit.isSuccess(exit) ? { tag: "Success", value: exit.value === undefined ? "undefined" : exit.value }
    : { tag: "Failure", cause: String(exit.cause) }
const settle = Effect.gen(function*() {
  for (let i = 0; i < 8; i++) yield* Effect.yieldNow
})
const out = { effect: version }

// R1. raceAll. Entrant A waits on a Deferred. Entrant B completes it and then waits for ever.
// A wins while B is still starting, so B is not yet in the race's set of fibers.
// Reading: rc.112 decides at the winner's resume that nothing needs a clean-up, and B is never
// interrupted. 4.0.1 decides at the race's exit, and interrupts B.
out.r1_raceLoserForkedDuringSettle = await Effect.runPromise(Effect.gen(function*() {
  const log = []
  const d = yield* Deferred.make()
  const a = Effect.andThen(Deferred.await(d), Effect.sync(() => "A"))
  const b = Effect.onInterrupt(
    Effect.andThen(Deferred.succeed(d, undefined), Effect.never),
    () => Effect.sync(() => { log.push("B interrupted") })
  )
  const winner = yield* Effect.raceAll([a, b])
  yield* settle
  return { winner, afterTheRace: log.length === 0 ? "B was not interrupted" : log.join(", ") }
}))

// R2. awaitAllChildren. A fiber forks a child that never ends, and then awaits its children.
// Reading: rc.112 awaits inside a masked finalizer, so an interrupt of the fiber does not end it.
// 4.0.1 restores interruptibility around the await.
out.r2_awaitAllChildrenInterrupted = await Effect.runPromise(Effect.gen(function*() {
  let child
  const x = yield* Effect.forkChild(
    Effect.awaitAllChildren(Effect.gen(function*() {
      child = yield* Effect.forkChild(Effect.never)
      return 1
    }))
  )
  yield* settle
  x.interruptUnsafe()
  yield* settle
  const afterInterrupt = x.pollUnsafe()
  // Let a still-waiting fiber finish, so the probe ends on both builds.
  child.interruptUnsafe()
  yield* settle
  return {
    afterInterrupt: afterInterrupt === undefined ? "still running" : show(afterInterrupt),
    afterChildEnded: x.pollUnsafe() === undefined ? "still running" : show(x.pollUnsafe())
  }
}))

// R3. The cancel effect of a callback dies while the fiber is interrupted.
// Reading: rc.112 answers the cancel effect's failure alone. 4.0.1 merges it into the interrupt.
out.r3_asyncCancelDies = await Effect.runPromise(Effect.gen(function*() {
  const y = yield* Effect.forkChild(Effect.callback(() => Effect.die("cancel boom")))
  yield* settle
  return show(yield* Fiber.interrupt(y).pipe(Effect.andThen(Fiber.await(y))))
}))

// R4. The operations that one combinator charges to the fiber's counter, inside one run-loop
// entry. `ops(X)` is the counter after X minus the counter before it, with the same harness
// around every X, so the row `succeed` is the harness alone.
// Reading: 4.0.1 pushes some frames directly and passes some values straight to the next
// continuation, so several combinators charge a different count.
const counter = Effect.withFiber((fiber) => Effect.succeed(fiber.currentOpCount))
const ops = (x) =>
  Effect.runPromise(Effect.flatMap(counter, (c0) => Effect.flatMap(x, () => Effect.flatMap(counter, (c1) => Effect.succeed(c1 - c0)))))
const one = Effect.succeed(1)
const subjects = {
  succeed: one,
  sync: Effect.sync(() => 1),
  suspend: Effect.suspend(() => one),
  map: Effect.map(one, (n) => n + 1),
  as: Effect.as(one, 2),
  asVoid: Effect.asVoid(one),
  flatMap: Effect.flatMap(one, () => one),
  andThen: Effect.andThen(one, one),
  tap: Effect.tap(one, () => one),
  zipWith: Effect.zipWith(one, one, (a, b) => a + b),
  exitOfSuccess: Effect.exit(one),
  exitOfFailure: Effect.exit(Effect.fail("e")),
  catchCauseOfSuccess: Effect.catchCause(one, () => one),
  catchCauseOfFailure: Effect.catchCause(Effect.fail("e"), () => one),
  matchCauseEffect: Effect.matchCauseEffect(one, { onSuccess: () => one, onFailure: () => one }),
  matchCause: Effect.matchCause(one, { onSuccess: () => 1, onFailure: () => 2 }),
  match: Effect.match(one, { onSuccess: () => 1, onFailure: () => 2 }),
  onExit: Effect.onExit(one, () => Effect.void),
  ensuring: Effect.ensuring(one, Effect.void),
  uninterruptible: Effect.uninterruptible(one),
  uninterruptibleMask: Effect.uninterruptibleMask((restore) => restore(one)),
  interruptible: Effect.uninterruptible(Effect.interruptible(one)),
  scoped: Effect.scoped(one),
  scopedAcquireRelease: Effect.scoped(Effect.acquireRelease(one, () => Effect.void)),
  scopedTwoReleases: Effect.scoped(Effect.andThen(Effect.acquireRelease(one, () => Effect.void), Effect.acquireRelease(one, () => Effect.void))),
  acquireUseRelease: Effect.acquireUseRelease(one, () => one, () => Effect.void),
  genThreeYields: Effect.gen(function*() {
    const a = yield* one
    const b = yield* one
    const c = yield* one
    return a + b + c
  }),
  forEachThree: Effect.forEach([1, 2, 3], () => one),
  withFiber: Effect.withFiber(() => one),
  provideService: Effect.provideService(one, Scheduler.MaxOpsBeforeYield, 2048),
  forkChildThenJoin: Effect.flatMap(Effect.forkChild(one, { startImmediately: true }), (f) => Fiber.join(f))
}
out.r4_opsCharged = {}
for (const [name, x] of Object.entries(subjects)) out.r4_opsCharged[name] = await ops(x)

// R5. Where the budget's yields land. Fiber A runs a chain of steps and notes each step. Fiber B
// was forked before with a deferred start; each time it runs it notes "B" and yields. So every "B"
// in the log marks a point where A gave up the thread. The budget is 64 operations.
// `yieldsAfterStep` lists, for each such point, the last step A had noted.
// Reading: rc.112 tests the budget before every step. 4.0.1 passes a mapped value straight to the
// next continuation, counts it, and tests the budget only when control returns to the loop.
const budgetRun = (steps, stepOf) =>
  Effect.runPromise(
    Effect.gen(function*() {
      const log = []
      yield* Effect.forkChild(Effect.gen(function*() {
        for (let i = 0; i < 40; i++) {
          log.push("B")
          yield* Effect.yieldNow
        }
      }))
      let chain = Effect.succeed(0)
      for (let i = 1; i <= steps; i++) chain = stepOf(chain, i, log)
      yield* chain
      log.push("A done")
      const end = log.indexOf("A done")
      const yieldsAfterStep = []
      for (let i = 0; i < end; i++) if (log[i] === "B") yieldsAfterStep.push(i === 0 ? 0 : (log[i - 1] === "B" ? yieldsAfterStep[yieldsAfterStep.length - 1] : log[i - 1]))
      return { yieldsAfterStep }
    }).pipe(Effect.provideService(Scheduler.MaxOpsBeforeYield, 64))
  )
out.r5_budgetYield_mapChain = await budgetRun(300, (chain, i, log) => Effect.map(chain, () => { log.push(i); return i }))
out.r5_budgetYield_flatMapChain = await budgetRun(300, (chain, i, log) =>
  Effect.flatMap(chain, () => Effect.sync(() => { log.push(i); return i })))
out.r5_budgetYield_tapChain = await budgetRun(300, (chain, i, log) => Effect.tap(chain, () => Effect.sync(() => { log.push(i) })))
out.r5_budgetYield_genLoop = await Effect.runPromise(
  Effect.gen(function*() {
    const log = []
    yield* Effect.forkChild(Effect.gen(function*() {
      for (let i = 0; i < 40; i++) {
        log.push("B")
        yield* Effect.yieldNow
      }
    }))
    for (let i = 1; i <= 300; i++) {
      yield* Effect.map(Effect.succeed(i), (n) => { log.push(n); return n })
    }
    log.push("A done")
    const end = log.indexOf("A done")
    const yieldsAfterStep = []
    for (let i = 0; i < end; i++) if (log[i] === "B") yieldsAfterStep.push(i === 0 ? 0 : (log[i - 1] === "B" ? yieldsAfterStep[yieldsAfterStep.length - 1] : log[i - 1]))
    return { yieldsAfterStep }
  }).pipe(Effect.provideService(Scheduler.MaxOpsBeforeYield, 64))
)

// R7. The message of a timeout.
out.r7_timeoutMessage = await Effect.runPromise(Effect.exit(Effect.timeout(Effect.never, 5))).then((exit) =>
  Exit.isSuccess(exit) ? show(exit) : { tag: "Failure", cause: String(exit.cause) })

console.log(JSON.stringify(out, null, 1))
