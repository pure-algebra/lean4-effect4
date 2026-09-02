import * as Effect from "effect/Effect"
import * as Fiber from "effect/Fiber"

function check(condition: boolean, message: string): asserts condition {
  if (!condition) throw new Error(message)
}

let cases = 0
function passed(name: string): void {
  cases++
  console.log(`PASS ${name}`)
}

// A synchronous success prevents the source loop from creating later fibers.
const starts: number[] = []
const immediateWinner = Effect.sync(() => { starts.push(0); return 11 })
const laterEntrant = Effect.sync(() => { starts.push(1); return 22 })
check(Effect.runSync(Effect.raceAll([immediateWinner, laterEntrant])) === 11,
  "the first immediate success must win")
check(JSON.stringify(starts) === "[0]", "the later entrant must not start")
passed("race-immediate-success-stops-launch")

// First success differs from first completion when an earlier entrant fails.
const retryStarts: number[] = []
const immediateFailure = Effect.gen(function*() {
  yield* Effect.sync(() => retryStarts.push(0))
  return yield* Effect.fail("first")
})
const laterSuccess = Effect.sync(() => { retryStarts.push(1); return 22 })
check(Effect.runSync(Effect.raceAll([immediateFailure, laterSuccess])) === 22,
  "a failed first completion must not win a first-success race")
check(JSON.stringify(retryStarts) === "[0,1]", "failure must allow later launch")
passed("race-failure-allows-next-launch")

const allFailed = Effect.runSyncExit(Effect.raceAll([
  Effect.fail("left"), Effect.fail("right"), Effect.fail("left")
]))
check(allFailed._tag === "Failure", "all-failure race must fail")
const errors = allFailed.cause.reasons.map(reason => {
  check(reason._tag === "Fail", "this corpus contains only typed failures")
  return reason.error
})
check(JSON.stringify(errors) === '["left","right","left"]',
  "race failure reasons must retain completion order and duplicates")
passed("race-all-failures-retain-order-and-duplicates")

const emptyRace = Effect.runFork(Effect.raceAll([]))
check(emptyRace.pollUnsafe() === undefined, "empty race must stay pending")
Effect.runSync(Fiber.interrupt(emptyRace))
check(emptyRace.pollUnsafe()?._tag === "Failure", "explicit cancellation must finish it")
passed("empty-race-pending-until-interrupted")

// The local body result exists before cleanup; the published Exit does not.
const closingOrder: string[] = []
const parentProgram = Effect.withFiber(parent => {
  const child = Effect.onExit(Effect.never, () => Effect.sync(() => {
    check(parent.pollUnsafe() === undefined, "parent published before child cleanup")
    closingOrder.push("child-cleanup")
  }))
  return Effect.gen(function*() {
    yield* Effect.forkChild(child, { startImmediately: true })
    closingOrder.push("parent-body")
    return 7
  })
})
const parent = Effect.runFork(parentProgram)
parent.addObserver(() => closingOrder.push("parent-observer"))
check(parent.pollUnsafe()?._tag === "Success", "parent should finish after this cleanup")
check(JSON.stringify(closingOrder) === '["parent-body","child-cleanup","parent-observer"]',
  "parent notification must follow child cleanup")
passed("parent-publishes-after-tracked-child-cleanup")

const daemonCleanup: string[] = []
const daemonBody = Effect.onExit(Effect.never,
  () => Effect.sync(() => { daemonCleanup.push("cleanup") }))
const daemon = Effect.runSync(Effect.forkDetach(daemonBody, { startImmediately: true }))
check(daemon.pollUnsafe() === undefined && daemonCleanup.length === 0,
  "the parent exit must leave its daemon running")
Effect.runSync(Fiber.interrupt(daemon))
check(JSON.stringify(daemonCleanup) === '["cleanup"]',
  "the explicit interrupt must run daemon cleanup exactly once")
passed("daemon-survives-parent-exit")

const failedFiber = Effect.runFork(Effect.fail("child-error"))
const awaited = Effect.runSyncExit(Fiber.await(failedFiber))
check(awaited._tag === "Success" && awaited.value._tag === "Failure",
  "await must deliver the failed Exit as a successful value")
const joined = Effect.runSyncExit(Fiber.join(failedFiber))
check(joined._tag === "Failure", "join must resume the failed Exit as an effect")
passed("await-value-distinct-from-join-effect")

// E4-CONC-CE-024: the winning callback tests the mutable tracked set before the currently
// starting fiber is inserted. Both branches of that test are observable.
function checkReentrantRace(hasEarlierLoser: boolean): void {
  const state: {
    resume?: (effect: Effect.Effect<string>) => void
    lateFiber?: Fiber.Fiber<unknown, unknown>
    cleanups: string[]
  } = { cleanups: [] }
  const earlierWinner = Effect.callback<string>(resume => { state.resume = resume })
  const parked = Effect.onExit(Effect.never,
    () => Effect.sync(() => { state.cleanups.push("parked") }))
  const late = Effect.withFiber(fiber => {
    state.lateFiber = fiber
    return Effect.gen(function*() {
      const resume = state.resume
      check(resume !== undefined, "earlier callback must be registered")
      resume(Effect.succeed("first-wins"))
      return yield* Effect.onExit(Effect.never,
        () => Effect.sync(() => { state.cleanups.push("late") }))
    })
  })
  const entrants = hasEarlierLoser
    ? [earlierWinner, parked, late]
    : [earlierWinner, late]
  check(Effect.runSync(Effect.raceAll(entrants)) === "first-wins",
    "reentrant completion must retain the earlier winner")
  const lateFiber = state.lateFiber
  check(lateFiber !== undefined, "the final entrant must have started")
  if (hasEarlierLoser) {
    check(lateFiber.pollUnsafe()?._tag === "Failure",
      "the deferred nonempty-set branch must include the late insertion")
    check(JSON.stringify(state.cleanups) === '["parked","late"]',
      "deferred cleanup must use the mutable set, not a winner-time snapshot")
    passed("race-reentrant-nonempty-set-includes-late-insertion")
  } else {
    check(lateFiber.pollUnsafe() === undefined && state.cleanups.length === 0,
      "the empty-set short circuit must leave the late insertion alive")
    Effect.runSync(Fiber.interrupt(lateFiber))
    check(JSON.stringify(state.cleanups) === '["late"]',
      "explicit cleanup must finish the otherwise surviving entrant")
    passed("race-reentrant-empty-set-bypasses-late-insertion")
  }
}
checkReentrantRace(false)
checkReentrantRace(true)

// E4-CONC-CE-025: the retained body result is a continuation payload. A new interrupt of the
// waiting parent can still change its eventual published Exit.
const interruptedWait: {
  release?: (effect: Effect.Effect<string>) => void
  child?: Fiber.Fiber<string>
} = {}
const heldChild = Effect.callback<string>(resume => { interruptedWait.release = resume })
const waitingParent = Effect.runFork(Effect.gen(function*() {
  interruptedWait.child = yield* Effect.forkChild(heldChild,
    { startImmediately: true, uninterruptible: true })
  return 7
}))
const heldFiber = interruptedWait.child
const releaseChild = interruptedWait.release
check(heldFiber !== undefined && releaseChild !== undefined,
  "the masked child must have reached its callback")
check(waitingParent.pollUnsafe() === undefined && heldFiber.pollUnsafe() === undefined,
  "the parent must wait for its masked child")
waitingParent.interruptUnsafe(99)
check(waitingParent.pollUnsafe() === undefined && heldFiber.pollUnsafe() === undefined,
  "requesting interruption must not count as a publication")
releaseChild(Effect.succeed("released"))
check(heldFiber.pollUnsafe()?._tag === "Success", "the explicitly released child must finish")
const interruptedParentExit = waitingParent.pollUnsafe()
check(interruptedParentExit?._tag === "Failure",
  "the new interrupt must replace the earlier body success")
check(interruptedParentExit.cause.reasons.length === 1 &&
  interruptedParentExit.cause.reasons[0]?._tag === "Interrupt" &&
  interruptedParentExit.cause.reasons[0].fiberId === 99,
  "the parent's publication must retain the requested interruptor")
passed("parent-interrupt-during-child-wait-changes-result")

check(cases === 10, "the complete finite corpus must execute")
console.log(`fiber-supervision-host: ${cases} finite cases passed`)
