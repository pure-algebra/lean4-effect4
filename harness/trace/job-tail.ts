/**
 * The host tail of the job runner: the first harness program whose service is
 * a real one.
 *
 * `Jobs` here is not a `Ref` standing in for a resource. `connect` makes a
 * temporary directory and writes the queue into a JSON file; `next`, `ack` and
 * `requeue` read that file, change it and write it back with `node:fs`;
 * `attempt` and `run` wait on a real timer (`Effect.sleep`) before answering,
 * so the scheduler is genuinely exercised; and `disconnect` deletes the
 * directory. The seeded per-job failure schedule lives in the file, so a
 * failure on the host is the same failure the Lean handler models.
 *
 * `next` hands out a *ticket*: the connection it dequeued from and the job id.
 * `run`, `ack` and `requeue` are two-parameter operations over that ticket, so
 * each of them reads the file through the connection it was handed rather than
 * through a module-level one. The flow performs them from a single request
 * slot holding the ticket, destructured at the call.
 *
 * `EFFECT4_PROGRAM` is the *golden* name (`jobRunner.clean`, `jobPoison.poison`,
 * …), not just the program name: four goldens share the `jobRunner` body and
 * differ only in their queue seed and their tapes, and the seed is what makes
 * a golden a golden. `scenarios` below is the host copy of `jobEntries` in
 * `harness/trace/Generate.lean`; the golden is the join of the two.
 *
 * `EFFECT4_TAPE` carries *both* tapes in one list. The choice sites the flow
 * author wrote are below `Effect4.Flow.interruptBase` and every interrupt site
 * is at or above it (`Point.site_ne_choose`), so the tail splits the list by
 * site into the `Decisions` reader and the `Interrupts` reader, and neither
 * ever answers the other's question.
 */
import { Effect, Result, type Exit } from "effect"
import { Decisions, Interrupts, Jobs, JobsRows, Regions } from "./job-fixture.ts"
import * as fixture from "./job-fixture.ts"
import {
  closeQueue,
  consumeFailure,
  failuresLeft,
  JobQueueBrand,
  jobError,
  openQueue,
  queueExists,
  readQueue,
  writeQueue,
  type JobQueue,
  type QueueState
} from "./job-queue.ts"
import {
  decisionsFromTape,
  outcomeWire,
  registerHandle,
  runTraced,
  traceService,
  windowRows,
  type Event
} from "./tracer.ts"

declare const process: { readonly env: Record<string, string | undefined> }

const patchedFrames: Array<Record<string, unknown>> = []
;(globalThis as any).__effect4Frame = (row: string, data: Record<string, unknown>) => {
  patchedFrames.push({ row, ...data })
}

// A connection is an opaque host handle: the wire says only its index.
registerHandle((value) => JobQueueBrand in value)

/** The first site reserved for interrupt points (`Effect4.Flow.interruptBase`). */
const interruptBase = 1000000

const name = process.env.EFFECT4_PROGRAM ?? "jobRunner.clean"
const maxOpsBeforeYield = Number(process.env.EFFECT4_MAX_OPS ?? "1000000")
const budget = Number(process.env.EFFECT4_BUDGET ?? "100000")

const entries: Array<readonly [number, boolean]> = (process.env.EFFECT4_TAPE ?? "")
  .split(",")
  .filter((entry) => entry.length > 0)
  .map((entry) => {
    const [site, branch] = entry.split(":")
    return [Number(site), branch === "1"] as const
  })
const choiceTape = entries.filter(([site]) => site < interruptBase)
const interruptTape = entries.filter(([site]) => site >= interruptBase)

const sink: Event[] = []
const decisions = decisionsFromTape(choiceTape, sink)

const regions = {
  enter: (region: number) => Effect.sync(() => { sink.push({ kind: "enter", region }) }),
  leave: (region: number, exit: Exit.Exit<unknown, unknown>) =>
    Effect.sync(() => { sink.push({ kind: "leave", region, outcome: outcomeWire(exit as any) }) }),
  finalizer: (region: number, exit: Exit.Exit<unknown, unknown>) =>
    Effect.sync(() => { sink.push({ kind: "finalizer", region, outcome: outcomeWire(exit as any) }) })
}

/** The interrupt tape, read exactly as `Effect4.Flow.interruptRead` reads it:
 * the head entry is consumed only when it names this site, and exhaustion
 * answers "not delivered". Masking is rc.112's own: a masked region is lowered
 * to `Effect.uninterruptible(Effect.scoped(...))`, so a request made inside it
 * is kept and delivered when the mask is restored. */
let cursor = 0
const readInterruptTape = (site: number): boolean => {
  const entry = interruptTape[cursor]
  if (entry === undefined) return false
  if (entry[0] !== site) return false
  cursor += 1
  return entry[1]
}

const interrupts = {
  point: (site: number) =>
    Effect.withFiber((fiber: any) => {
      const answered = readInterruptTape(site)
      sink.push({ kind: "decide", site, branch: answered })
      if (answered) fiber.interruptUnsafe()
      return Effect.void
    })
}

/** How long a job takes. A real timer, so the run really suspends and the
 * scheduler really resumes it; a few milliseconds keeps the gate fast. */
const jobDuration = "2 millis"

/** The one connection a run opens, kept so the report can say whether the
 * release actually closed it. `attempt` is the only operation that still reads
 * it: it names the job alone, and a flow cannot pair the connection back on. */
let connection: JobQueue | null = null

const live = (seed: QueueState) => ({
  connect: Effect.sync(() => {
    connection = openQueue(seed)
    return connection
  }),
  next: (conn: JobQueue) =>
    Effect.sync(() => {
      const state = readQueue(conn)
      const job = state.pending[0]
      if (job === undefined) return [conn, 0] as const
      writeQueue(conn, { ...state, pending: state.pending.slice(1) })
      return [conn, job] as const
    }),
  run: (conn: JobQueue, job: number) =>
    Effect.gen(function* () {
      yield* Effect.sleep(jobDuration)
      const state = readQueue(conn)
      if (failuresLeft(state, job) === 0) return job
      writeQueue(conn, consumeFailure(state, job))
      return yield* Effect.fail(jobError(job))
    }) as Effect.Effect<number, string>,
  attempt: (job: number) =>
    Effect.gen(function* () {
      yield* Effect.sleep(jobDuration)
      const conn = connection!
      const state = readQueue(conn)
      if (failuresLeft(state, job) === 0) return Result.succeed(job)
      writeQueue(conn, consumeFailure(state, job))
      return Result.fail(jobError(job))
    }) as Effect.Effect<Result.Result<number, string>>,
  ack: (conn: JobQueue, job: number) =>
    Effect.sync(() => {
      const state = readQueue(conn)
      writeQueue(conn, { ...state, acked: [...state.acked, job] })
    }),
  requeue: (conn: JobQueue, job: number) =>
    Effect.sync(() => {
      const state = readQueue(conn)
      writeQueue(conn, {
        ...state,
        pending: [...state.pending, job],
        requeued: [...state.requeued, job]
      })
    }),
  disconnect: (conn: JobQueue) => Effect.sync(() => { closeQueue(conn) })
})

type Body = (n: number) => Effect.Effect<number, string, Jobs | Regions | Decisions | Interrupts>

const lowered = fixture as unknown as Record<string, Body>

/** The host copy of `jobEntries` in `harness/trace/Generate.lean`: which body
 * a golden runs, with which attempt budget, from which queue. */
const scenarios: Record<string, { body: string; input: number; seed: QueueState }> = {
  "jobRunner.clean": {
    body: "jobRunner", input: 2,
    seed: { pending: [1, 2, 3], acked: [], requeued: [], failures: [] }
  },
  "jobRunner.retry": {
    body: "jobRunner", input: 2,
    seed: { pending: [1, 2], acked: [], requeued: [], failures: [[2, 1]] }
  },
  "jobRunner.requeue": {
    body: "jobRunner", input: 2,
    seed: { pending: [2], acked: [], requeued: [], failures: [[2, 3]] }
  },
  "jobRunner.interrupt": {
    body: "jobRunner", input: 2,
    seed: { pending: [1, 2, 3], acked: [], requeued: [], failures: [] }
  },
  "jobRunnerMasked.masked": {
    body: "jobRunnerMasked", input: 2,
    seed: { pending: [1, 2], acked: [], requeued: [], failures: [] }
  },
  "jobPoison.poison": {
    body: "jobPoison", input: 2,
    seed: { pending: [7], acked: [], requeued: [], failures: [[7, 1]] }
  }
}

const scenario = scenarios[name]
if (scenario === undefined) throw new Error(`unknown job golden ${name}`)
const body = lowered[scenario.body]
if (body === undefined) throw new Error(`unknown job program ${scenario.body}`)

const program = Effect.gen(function* () {
  const service = traceService(JobsRows, live(scenario.seed), sink)
  sink.push({ kind: "phase", phase: "run" })
  return yield* body(scenario.input).pipe(
    Effect.provideService(Jobs, service),
    Effect.provideService(Regions, regions),
    Effect.provideService(Decisions, decisions),
    Effect.provideService(Interrupts, interrupts)
  )
})

const report = await runTraced(program, sink, { budget, maxOpsBeforeYield })
sink.push({ kind: "phase", phase: "teardown" })
// Whether the connection's directory is gone: the release ran on every path,
// the interrupted one included. Recorded, never compared.
const released = connection === null ? null : !queueExists(connection)
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
  patchedFrames,
  released,
  foreign: ["succ@./atoms.ts", "dec@./atoms.ts", "snd@./atoms.ts"]
}))
