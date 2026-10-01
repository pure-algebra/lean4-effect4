/**
 * Program 3 (seat PROGRAMS, 2026-09-30): a background worker pool draining a bounded queue with
 * bounded concurrency (three workers), each worker holding a resource that is released on any
 * exit, interruption included. Idiomatic Effect rc.112.
 *
 * rc.112 lines relied on (vendor/effect-4.0.0-rc.112/src/):
 *   Queue.bounded / offer / take   Queue.ts:500, :645, :1474 (state and wakes :343-386, :448-468,
 *                                  :1955-1975: the taker release runs on the dispatcher stored at make)
 *   Deferred.make / succeed / await Deferred.ts:171, :1449, :223
 *   Ref.make / update / modify     Ref.ts:173, :1200, :797
 *   Effect.acquireRelease          Effect.ts:12928-12932 (release (a, Exit<unknown, unknown>) => Effect<unknown, never>)
 *   Effect.scoped                  Effect.ts:12815
 *   Effect.onInterrupt             Effect.ts:14227
 *   Effect.forever                 Effect.ts:14480
 *   Effect.forEach (concurrency)   Effect.ts:1088; internal/effect.ts:4648-4690 (concurrency > 1 goes
 *                                  to forEachConcurrent, an eager fork-and-observe loop)
 *   Effect.forkChild               Effect.ts:16990
 *   Fiber.interrupt                Fiber.ts:354 (waits for the target to finish its finalizers)
 *   Effect.sleep                   Effect.ts:8696
 */
import { Data, Deferred, Effect, Fiber, Queue, Ref } from "effect"

/** A job: a record. */
interface Job {
  readonly id: number
  readonly payload: string
}

export class JobFailed extends Data.TaggedError("JobFailed")<{
  readonly id: number
  readonly reason: string
}> {}

/** What each worker holds while it runs: a resource with an identity. */
interface Conn {
  readonly worker: number
}

type Log = Ref.Ref<ReadonlyArray<string>>

const note = (log: Log, line: string) => Ref.update(log, (lines) => [...lines, line])

/** Open a connection; close it on any exit. The release sees the exit (rc.112 types it
 * `Exit<unknown, unknown>`). */
const openConn = (worker: number, log: Log) =>
  Effect.acquireRelease(
    Effect.as(note(log, `open ${worker}`), { worker } satisfies Conn),
    (conn, exit) => note(log, `close ${conn.worker} ${exit._tag}`)
  )

const work = (log: Log, conn: Conn, job: Job) =>
  Effect.gen(function*() {
    yield* Effect.sleep("10 millis")
    if (job.payload === "bad") {
      return yield* Effect.fail(new JobFailed({ id: job.id, reason: "bad payload" }))
    }
    yield* note(log, `done ${job.id} by ${conn.worker}`)
  })

/** Count one finished job; the last one completes the gate. `Ref.modify` decides "last" and
 * counts in one atomic step. */
const finish = (count: Ref.Ref<number>, total: number, allDone: Deferred.Deferred<void>) =>
  Ref.modify(count, (n): [boolean, number] => [n + 1 === total, n + 1]).pipe(
    Effect.flatMap((last) => last ? Deferred.succeed(allDone, undefined) : Effect.void)
  )

/** One worker: hold a connection for its whole life, take jobs forever, keep going past a
 * failed job, log its interruption. */
const worker = (
  id: number,
  queue: Queue.Dequeue<Job>,
  log: Log,
  count: Ref.Ref<number>,
  total: number,
  allDone: Deferred.Deferred<void>
) =>
  Effect.scoped(
    Effect.gen(function*() {
      const conn = yield* openConn(id, log)
      return yield* Effect.forever(
        Effect.gen(function*() {
          const job = yield* Queue.take(queue)
          yield* work(log, conn, job).pipe(
            Effect.catchTag("JobFailed", (e) => note(log, `failed ${e.id}: ${e.reason}`))
          )
          yield* finish(count, total, allDone)
        })
      )
    })
  ).pipe(Effect.onInterrupt(() => note(log, `stopped ${id}`)))

export const program = Effect.gen(function*() {
  const jobs: ReadonlyArray<Job> = [
    { id: 1, payload: "a" },
    { id: 2, payload: "bad" },
    { id: 3, payload: "c" },
    { id: 4, payload: "d" },
    { id: 5, payload: "e" }
  ]
  const queue = yield* Queue.bounded<Job>(2)
  const log = yield* Ref.make<ReadonlyArray<string>>([])
  const count = yield* Ref.make(0)
  const allDone = yield* Deferred.make<void>()
  const pool = yield* Effect.forkChild(
    Effect.forEach(
      [1, 2, 3],
      (id) => worker(id, queue, log, count, jobs.length, allDone),
      { concurrency: 3, discard: true }
    )
  )
  yield* Effect.forEach(jobs, (job) => Queue.offer(queue, job), { discard: true })
  yield* Deferred.await(allDone)
  yield* Fiber.interrupt(pool) // every worker's release runs, with an interrupt exit
  return yield* Ref.get(log)
})

/** The checked type, pinned: nothing fails, nothing is required. */
export const pinProgram: Effect.Effect<ReadonlyArray<string>> = program
