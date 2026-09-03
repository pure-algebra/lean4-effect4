import { Deferred, Effect, Option, Result } from "effect"
import {
  Deferreds,
  DeferredsRows,
  deferredDoubleComplete,
  deferredFailAwait,
  deferredPendingAwait,
  deferredPollPending,
  deferredSucceedAwait,
  deferredTwoHandles
} from "./deferred-fixture.ts"
import { registerHandle, runTraced, traceService, windowRows, type Event } from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

/**
 * The host face of the `Deferreds` family: rc.112's own `Deferred`, wrapped so
 * the shared alphabet can see it.
 *
 * - `make` is `Deferred.make`, `succeed`/`fail` are `Deferred.succeed`/`fail`
 *   and answer whether this call completed the cell, `isDone` is
 *   `Deferred.isDone`.
 * - `poll` is the only method that is not a `Deferred` call verbatim: rc.112's
 *   `Deferred.poll` answers `Option<Effect<A, E>>`, the completion *effect*,
 *   while the family answers the completion *value*. Running that effect
 *   through `Effect.result` is total and observes nothing — the cell is
 *   already completed, so the effect is a `succeed`/`fail` — and lands in
 *   exactly the `Option<Result<number, number>>` the family declares.
 * - `awaitValue` is `Deferred.await`; `awaitError` is `Effect.flip` of it, so
 *   the failure is the answer and the value is the abort.
 *
 * A cell never reaches the wire as an object. `registerHandle` brands it and
 * `wire` encodes it as its index in first-seen order, which is the `make` order
 * the Lean face numbers cells in.
 *
 * `deferredPendingAwait` awaits a cell nothing completes. rc.112 parks the
 * fiber (`Deferred.ts` `_await` pushes a resume onto `self.resumes`), no
 * primitive runs after that, so the op budget cannot fire and the run never
 * settles. `stallMs` turns that park into the frontier the golden records
 * (`RunOptions.stallMs` in `tracer.ts`).
 */

// The brand rc.112 stamps on every deferred (`Deferred.ts` TypeId). It is a
// string key, not an exported value, so it is written out here.
const DeferredTypeId = "~effect/Deferred"
registerHandle((value) => DeferredTypeId in value)

const name = process.env.EFFECT4_PROGRAM ?? "deferredSucceedAwait"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")
const stallMs = Number(process.env.EFFECT4_STALL_MS ?? "50")
const sink: Event[] = []

/** The completion a `poll` found, as the family's answer. */
const polled = (
  cell: Deferred.Deferred<number, number>
): Effect.Effect<Option.Option<Result.Result<number, number>>> =>
  Effect.flatMap(Deferred.poll(cell), (completion) =>
    Option.isNone(completion)
      ? Effect.succeed(Option.none<Result.Result<number, number>>())
      : Effect.asSome(Effect.result(completion.value)))

const live = {
  make: Deferred.make<number, number>(),
  succeed: (cell: Deferred.Deferred<number, number>, value: number) => Deferred.succeed(cell, value),
  fail: (cell: Deferred.Deferred<number, number>, error: number) => Deferred.fail(cell, error),
  isDone: (cell: Deferred.Deferred<number, number>) => Deferred.isDone(cell),
  poll: (cell: Deferred.Deferred<number, number>) => polled(cell),
  awaitValue: (cell: Deferred.Deferred<number, number>) => Deferred.await(cell),
  awaitError: (cell: Deferred.Deferred<number, number>) => Effect.flip(Deferred.await(cell))
}

/** Build the service before the `run` sentinel so construction is outside the
 * compared window; the cells themselves are minted by `make`, inside it. */
const deferredProgram = (
  body: (n: number) => Effect.Effect<number, number, Deferreds>,
  argument: number
) =>
  Effect.gen(function* () {
    const service = traceService(DeferredsRows, live, sink)
    sink.push({ kind: "phase", phase: "run" })
    return yield* body(argument).pipe(Effect.provideService(Deferreds, service))
  })

const programs: Record<string, Effect.Effect<number, number, never>> = {
  deferredSucceedAwait: deferredProgram(deferredSucceedAwait, 7),
  deferredFailAwait: deferredProgram(deferredFailAwait, 5),
  deferredDoubleComplete: deferredProgram(deferredDoubleComplete, 4),
  deferredPollPending: deferredProgram(deferredPollPending, 6),
  deferredTwoHandles: deferredProgram(deferredTwoHandles, 8),
  deferredPendingAwait: deferredProgram(deferredPendingAwait, 1)
}
/** The one program whose run parks; every other program must settle on its own. */
const stalls = name === "deferredPendingAwait"

const program = programs[name]
if (program === undefined) throw new Error(`unknown program ${name}`)

const report = await runTraced(
  program,
  sink,
  stalls ? { budget, maxOpsBeforeYield, stallMs } : { budget, maxOpsBeforeYield }
)
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
  expectYields: process.env.EFFECT4_EXPECT_YIELDS === "1",
  foreign: ["flagToNat@./atoms.ts", "pollValue@./atoms.ts", "addNat@./atoms.ts"]
}))
