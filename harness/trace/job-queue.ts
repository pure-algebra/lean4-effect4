/**
 * The real job queue the `Jobs` family talks to: a JSON file in a temporary
 * directory, written and read with `node:fs` on every operation.
 *
 * There is no in-memory shortcut here. `connect` makes a directory and writes
 * the seed; `next`, `ack` and `requeue` read the file, change it and write it
 * back; `disconnect` deletes the directory. So the queue state genuinely
 * survives from one operation to the next through the file system, and a run
 * that never reaches its `disconnect` leaves the directory behind — which is
 * exactly what the region's release exists to prevent, and what the
 * interrupted goldens check.
 *
 * The Lean face of the same state is `Queue` in `harness/trace/Generate.lean`,
 * with the same four fields and the same operations; the goldens are the join.
 *
 * A `JobQueue` never reaches the wire as an object: `job-tail.ts` brands it
 * with `registerHandle` and `tracer.ts` encodes it as its index in first-seen
 * order, which is the `Handle "JobQueue"` carrier on the Lean side.
 */
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { dirname, join } from "node:path"

/** The four fields the Lean `Queue` structure carries, in the same order. */
export interface QueueState {
  /** job ids still to run, front first */
  pending: number[]
  /** job ids acknowledged, in acknowledgement order */
  acked: number[]
  /** job ids put back on the queue, in that order */
  requeued: number[]
  /** how many more times each job is scheduled to fail */
  failures: Array<[number, number]>
}

/** The brand the tail registers so a connection is wired as a handle index. */
export const JobQueueBrand = "__effect4JobQueue"

/** An open connection: the path of the JSON file holding the queue. */
export interface JobQueue {
  readonly __effect4JobQueue: true
  readonly path: string
}

/** Open a connection: make a temporary directory and write the seed into it. */
export const openQueue = (seed: QueueState): JobQueue => {
  const directory = mkdtempSync(join(tmpdir(), "effect4-jobs-"))
  const path = join(directory, "queue.json")
  writeFileSync(path, JSON.stringify(seed), "utf8")
  return { [JobQueueBrand]: true, path } as JobQueue
}

export const readQueue = (queue: JobQueue): QueueState =>
  JSON.parse(readFileSync(queue.path, "utf8")) as QueueState

export const writeQueue = (queue: JobQueue, state: QueueState): void => {
  writeFileSync(queue.path, JSON.stringify(state), "utf8")
}

/** Close a connection: delete the directory the queue lives in. */
export const closeQueue = (queue: JobQueue): void => {
  rmSync(dirname(queue.path), { recursive: true, force: true })
}

/** Whether the connection's directory is still there. A run whose release ran
 * leaves nothing behind; this is what the tail reports as `released`. */
export const queueExists = (queue: JobQueue): boolean => {
  try {
    readFileSync(queue.path, "utf8")
    return true
  } catch {
    return false
  }
}

/** How many more times a job is scheduled to fail. */
export const failuresLeft = (state: QueueState, job: number): number => {
  const entry = state.failures.find(([id]) => id === job)
  return entry === undefined ? 0 : entry[1]
}

/** Spend one scheduled failure of a job. */
export const consumeFailure = (state: QueueState, job: number): QueueState => ({
  ...state,
  failures: state.failures.map(([id, left]) => (id === job ? [id, left - 1] : [id, left]))
})

/** The message a failed job reports; `jobError` in `Generate.lean` builds the
 * same string, and the goldens compare them byte for byte. */
export const jobError = (job: number): string => `job ${job} failed`
