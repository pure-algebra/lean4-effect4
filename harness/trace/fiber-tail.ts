import { Effect, Fiber, Option } from "effect"
import {
  Fibers,
  FibersRows,
  fiberAwaitValueDistinctFromJoinEffect,
  fiberDaemonSurvivesParentExit,
  fiberEmptyRacePendingUntilInterrupted,
  fiberParentInterruptDuringChildWait,
  fiberParentPublishesAfterChildCleanup,
  fiberRaceAllFailuresRetainOrder,
  fiberRaceFailureAllowsNextLaunch,
  fiberRaceImmediateSuccessStopsLaunch,
  fiberRaceReentrantEmptySetBypasses
} from "./fiber-fixture.ts"
import { registerHandle, runTraced, traceService, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/**
 * The host face of the `Fibers` family: two rc.112 fibers, with the tape
 * choosing which of them holds the processor.
 *
 * - `fork` is `Effect.forkChild(body, { startImmediately: false })` and
 *   `forkDetach` is `Effect.forkDetach(body, { startImmediately: false })`:
 *   the child is queued and nothing of it runs yet. The fork then reads one
 *   entry off the tape, records it as a `decide` row, and on `true` arms
 *   `TapeScheduler.shouldYield` (`tracer.ts`) and spends one primitive, so the
 *   run loop takes the processor away and drains its queue. On `false` the
 *   parent keeps the processor and the child stays queued. The site is the
 *   fork's ordinal, which is what the Lean face numbers its forks by.
 * - `join` is `Fiber.join`: a failed child's error is resumed in this fiber,
 *   so the run ends failed. `awaitValue` and `awaitError` are both
 *   `Fiber.await`, projecting the `Exit` onto its success value and its typed
 *   failure; an interrupted child answers `Option.none()` to both, which is
 *   how this alphabet spells the third arm of an `Exit` (see the module
 *   comment of `Effect4/Concurrency/FiberFamily.lean`).
 * - `interrupt` is `Fiber.interrupt`.
 * - `started` and `cleanups` read the two arrays the bodies append to. They
 *   are `Effect.sync`, so they never hand the processor over.
 *
 * The bodies are the same numeric table the Lean face carries: 0 succeeds with
 * 11, 1 with 22, 2 fails with 1, 3 fails with 2, and anything else is
 * `Effect.never`. Every body appends its code to `started` when it is given
 * the processor and to `cleanups` when its `onExit` runs, so start order,
 * cleanup order and duplicates are all observable at the service level.
 *
 * A fiber never reaches the wire as an object: `registerHandle` brands it and
 * `wire` encodes it as its index in first-seen order, which is the fork order
 * the Lean face numbers children in.
 */

// The brand rc.112 stamps on every fiber (`internal/effect.ts` FiberTypeId).
const FiberTypeId = "~effect/Fiber"
registerHandle((value) => FiberTypeId in value)

const started: number[] = []
const cleanups: number[] = []

/** The child body table, shared with `bodyOutcome` in the Lean module. */
const body = (code: number): Effect.Effect<number, number> => {
  const core: Effect.Effect<number, number> =
    code === 0
      ? Effect.succeed(11)
      : code === 1
      ? Effect.succeed(22)
      : code === 2
      ? (Effect.fail(1) as Effect.Effect<number, number>)
      : code === 3
      ? (Effect.fail(2) as Effect.Effect<number, number>)
      : (Effect.never as unknown as Effect.Effect<number, number>)
  return Effect.onExit(
    Effect.flatMap(Effect.sync(() => { started.push(code) }), () => core),
    () => Effect.sync(() => { cleanups.push(code) })
  )
}

const name = process.env.EFFECT4_PROGRAM ?? "raceImmediateSuccessStopsLaunch"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const sink: Event[] = []

/** The decision tape, in the golden's own spelling: `site:1` for a fork that
 * hands the processor to the run loop, `site:0` for one that does not. */
const tape: Array<readonly [number, boolean]> = (process.env.EFFECT4_TAPE ?? "")
  .split(",")
  .filter((entry) => entry.length > 0)
  .map((entry) => {
    const [site, branch] = entry.split(":")
    return [Number(site), branch === "1"] as const
  })

class TapeExhausted extends Error { readonly _tag = "TAPE_EXHAUSTED" }
class TapeSiteMismatch extends Error { readonly _tag = "TAPE_SITE_MISMATCH" }

let cursor = 0
/** Answer the fork at the next site from the tape and record the `decide` row. */
const decide = (): boolean => {
  const entry = tape[cursor]
  if (entry === undefined) throw new TapeExhausted(`fork site ${cursor} past the end of the tape`)
  if (entry[0] !== cursor) throw new TapeSiteMismatch(`wanted site ${cursor}, tape has ${entry[0]}`)
  cursor += 1
  sink.push({ kind: "decide", site: entry[0], branch: entry[1] })
  return entry[1]
}

/** Armed by a `true` decision, consumed by `TapeScheduler.shouldYield`. */
let armed = false
const consumeArmed = (): boolean => {
  if (!armed) return false
  armed = false
  return true
}

/** The shared fork body: queue the child, answer the tape, and on `true` spend
 * one primitive with the scheduler armed so the run loop drains its queue. */
const forkWith = (
  fork: (child: Effect.Effect<number, number>) => Effect.Effect<Fiber.Fiber<number, number>>,
  code: number
) =>
  Effect.gen(function* () {
    const fiber = yield* fork(body(code))
    if (decide()) {
      armed = true
      yield* Effect.sync(() => {})
    }
    return fiber
  })

const live = {
  fork: (code: number) =>
    forkWith((child) => Effect.forkChild(child, { startImmediately: false }), code),
  forkDetach: (code: number) =>
    forkWith((child) => Effect.forkDetach(child, { startImmediately: false }), code),
  join: (fiber: Fiber.Fiber<number, number>) => Fiber.join(fiber),
  awaitValue: (fiber: Fiber.Fiber<number, number>) =>
    Effect.map(Fiber.await(fiber), (exit) =>
      exit._tag === "Success" ? Option.some(exit.value) : Option.none()),
  awaitError: (fiber: Fiber.Fiber<number, number>) =>
    Effect.map(Fiber.await(fiber), (exit) => {
      if (exit._tag === "Success") return Option.none<number>()
      const reasons = ((exit as any).cause?.reasons ?? []) as ReadonlyArray<{ _tag: string; error?: unknown }>
      const fail = reasons.find((reason) => reason._tag === "Fail")
      return fail === undefined ? Option.none<number>() : Option.some(fail.error as number)
    }),
  interrupt: (fiber: Fiber.Fiber<number, number>) => Fiber.interrupt(fiber),
  started: Effect.sync(() => started.slice()),
  cleanups: Effect.sync(() => cleanups.slice())
}

// `lowered`, not `body`: the child-body table above owns that name here.
const fiberProgram = (lowered: (n: number) => Effect.Effect<unknown, number, Fibers>) =>
  Effect.gen(function* () {
    const service = traceService(FibersRows, live, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* lowered(0).pipe(Effect.provideService(Fibers, service))
  })

const programs: Record<string, Effect.Effect<unknown, number, never>> = {
  raceImmediateSuccessStopsLaunch: fiberProgram(fiberRaceImmediateSuccessStopsLaunch),
  raceFailureAllowsNextLaunch: fiberProgram(fiberRaceFailureAllowsNextLaunch),
  raceAllFailuresRetainOrder: fiberProgram(fiberRaceAllFailuresRetainOrder),
  emptyRacePendingUntilInterrupted: fiberProgram(fiberEmptyRacePendingUntilInterrupted),
  parentPublishesAfterChildCleanup: fiberProgram(fiberParentPublishesAfterChildCleanup),
  daemonSurvivesParentExit: fiberProgram(fiberDaemonSurvivesParentExit),
  awaitValueDistinctFromJoinEffect: fiberProgram(fiberAwaitValueDistinctFromJoinEffect),
  raceReentrantEmptySetBypasses: fiberProgram(fiberRaceReentrantEmptySetBypasses),
  parentInterruptDuringChildWait: fiberProgram(fiberParentInterruptDuringChildWait)
}
const program = programs[name]
if (program === undefined) throw new Error(`unknown program ${name}`)

const report = await runTraced(program as Effect.Effect<unknown, never, never>, sink, {
  budget,
  maxOpsBeforeYield,
  armed: consumeArmed
})
sink.push({ kind: "phase", phase: "teardown" })
console.log(JSON.stringify({
  rows: windowRows(report.events),
  frames: report.frames,
  exitTag: report.exitTag,
  primitives: report.primitives,
  yields: report.yields,
  scheduled: report.scheduled,
  tracerDefect: report.tracerDefect,
  maxOpsBeforeYield,
  // A two-fiber run yields by construction: every `true` on the tape is one
  // handover, and the driver's single-fiber yield check does not apply.
  expectYields: true,
  foreign: []
}))
