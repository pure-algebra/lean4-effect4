/** The host's side of a scenario's observation (decisions row 254). Each entry of a battery's
 * `Observation` has one source of evidence on the host, and this file names it.
 *
 *  - `measured`: the host measures the entry by itself, from the root's exit and the
 *    recorder's ledger, in a run with no reader.
 *  - `predicted`: the entry holds the session's refusals. The recorder's ledger predicts each
 *    one, in a run with no reader, and the lane's check compares each prediction with the
 *    verdict that Lean's replay gives the same record. The verdict itself is replay evidence.
 *  - `through` a reader: the host measures the entry through a note inside the program's state,
 *    at the script's end. A reader is on only where Lean grants it for the run
 *    (`Keyed.lean`, `readersOf`), and the lane's check compares the run with its readers and
 *    the run without one.
 *  - none of them: the entry waits. Lean's replay of the recording is its only evidence, and
 *    the scenario's whole-observation comparison waits for it.
 *
 * Each entry is written in the JSON that `Keyed.lean` writes for it, so the check compares the
 * two values. */
import type { HeldCall, KeyedRecorder, LedgerRefusal } from "./keyed-recorder.ts"
import type { Key } from "./keyed-protocol.ts"
import type { Json } from "./protocol.ts"

/** One act of a script: a row of the script's journal, as a record of the lane's wire. */
export type ScenarioAct =
  | { kind: "evaluate"; fiber: number }
  | { kind: "flush" }
  | { kind: "advanceClock"; millis: string }
  | { kind: "cancel"; fiber: number }
  | ({ kind: "call"; callId: number; row: number; request: Json } & Key)
  | ({ kind: "reply"; callId: number; completion: Json } & Key)
  | ({ kind: "apply" } & Key)
/** The readers that Lean grants a run, each with what the host must find: the count of cells,
 * the count of forked fibers. */
export interface Readers { cells?: number; fibers?: number; sleeps?: true; dispatchers?: true }
export type ReaderName = keyof Readers
/** One host run of a scenario, as `Keyed.lean scenarios` writes it. */
export interface ScenarioFixture {
  name: string; scenario: string; session: string
  module: string; namespaces: string[]; bindings: string; table: Json[]
  calls: Array<Key & { row: number; request: Json }>
  acts: ScenarioAct[]
  observation: Record<string, Json>
  /** The observation's entries, in the order of the battery's fields. */
  fields: string[]
  readers: Readers
  refusedReaders: Array<{ reader: ReaderName; why: string }>
  /** Each reader's premise on the run, asked for or not: `true`, or the reason it fails. */
  premises: Record<ReaderName, true | string>
}
export interface ScenarioManifest { runs: ScenarioFixture[]; waiting: Array<{ name: string; scenario: string; why: string }> }
/** What the host holds at a script's end. The last four are a reader's notes, in the wire. */
export interface HostEnd {
  /** The root fiber's exit, or `null` while the root is live. */
  readonly exit: Json
  readonly ledger: ReturnType<KeyedRecorder["measurements"]>
  /** The value of each cell that the module made, in the order it made them. */
  readonly cells?: Json[]
  /** The exit of each fiber of the machine by its number, the root first; `null` while live. */
  readonly fibers?: Json[]
  /** Each pending sleep: its fiber of the machine and its wake time. */
  readonly sleeps?: Array<[fiber: number, wake: string]>
  /** The count of armed dispatchers. */
  readonly armed?: number
}
/** The host's result for one script. */
export interface ScenarioResult {
  name: string; scenario: string
  /** Measured on the host with no reader, at the script's end. */
  measured: Record<string, Json>
  /** Predicted by the recorder's ledger with no reader: the session's refusals. */
  predicted: Record<string, Json>
  /** Measured on the host through the named reader, at the script's end. */
  through: Record<string, { reader: ReaderName; value: Json }>
  /** No measurement on the host: Lean's replay is the only evidence. */
  waits: Array<{ field: string; why: string }>
  /** The entries of `measured` and `predicted` again, from the run with its readers and the
   * exact wait. */
  withReaders: Record<string, Json>
  /** The root fiber's exit in the plain run and in the run with its readers. The readers'
   * control compares the two. It is no entry of an observation unless a battery reads it. */
  rootExits: [plain: Json, withReaders: Json]
  /** What each reader gives in a run that has that reader alone, with the plain run's scheduler
   * and wait: its entries, and the root's exit. The readers' control compares them with the
   * run that has every reader. */
  alone: { [Reader in ReaderName]?: { rootExit: Json; entries: Record<string, Json> } }
  /** The ledger's predictions of a refusal, by the record's index. */
  predictions: LedgerRefusal[]
  records: number
}

type Entries = Record<string, Json>
interface Scenario {
  /** The entries that the host gives with no reader: measured, or predicted by the ledger. */
  readonly host: (end: HostEnd, spelling: (call: HeldCall) => string) => Entries
  /** The entries of `host` that are the ledger's predictions of the session's refusals. */
  readonly predicted?: string[]
  /** The entries that the host measures through a reader, by the reader. */
  readonly through: { readonly [Reader in ReaderName]?: { readonly fields: string[]; readonly read: (end: HostEnd) => Entries } }
}
/** The entries of a log cell (`entries` of the batteries): the list, or nothing. */
const entries = (cell: Json | undefined): Json => Array.isArray(cell) ? cell : []
const key = ({ fiber, token }: Key): Json => ({ fiber, token })
/** An exit as the timeout battery reads one: a body, one tagged failure, or `other`. With
 * `interrupted`, one interruption is an ending of its own (`endingOf`); a held call's fate has
 * no such case (`fateOf`). */
const ending = (exit: Json, single: "interrupted" | "other"): Json => {
  if (exit === null || typeof exit !== "object" || Array.isArray(exit)) return { other: true }
  if (Object.hasOwn(exit, "success")) return { answered: exit.success! }
  const reasons = exit.failure
  const reason = Array.isArray(reasons) && reasons.length === 1 ? reasons[0] : undefined
  if (reason === undefined || reason === null || typeof reason !== "object" || Array.isArray(reason)) return { other: true }
  const failed = reason.fail
  if (Array.isArray(failed) && failed.length === 2 && failed.every(part => typeof part === "string")) return { failed }
  return single === "interrupted" && Object.hasOwn(reason, "interrupt") ? { interrupted: true } : { other: true }
}
/** A request's outcome as the atomic battery reads a fiber's exit (`outcomeOf`). */
const outcome = (exit: Json | undefined): Json => {
  if (exit === undefined || exit === null) return { pending: true }
  if (typeof exit !== "object" || Array.isArray(exit)) return { other: true }
  if (Object.hasOwn(exit, "success")) return exit.success === true ? { admitted: true } : exit.success === false ? { rejected: true } : { other: true }
  const reasons = exit.failure
  const reason = Array.isArray(reasons) && reasons.length === 1 ? reasons[0] : undefined
  if (reason === undefined || reason === null || typeof reason !== "object" || Array.isArray(reason)) return { other: true }
  const failed = reason.fail
  if (Array.isArray(failed) && failed.length === 2 && failed[0] === "Downstream" && failed[1] === "unavailable") return { failedBehind: true }
  return Object.hasOwn(reason, "interrupt") ? { interrupted: reason.interrupt! } : { other: true }
}
const scenarios: Record<string, Scenario> = {
  // Test/Dogfood/Scenario/Routing.lean, `Observation`. The refused rows are the session's: the
  // ledger predicts each one.
  routing: {
    host: ({ exit, ledger }, spelling) => ({
      outcome: exit,
      repositoryCalls: ledger.held.filter(call => spelling(call) === "UserRepo.findById").map(call => call.request),
      refusals: ledger.refusals.map(({ row, reason }) => [row, reason])
    }),
    predicted: ["refusals"],
    through: {}
  },
  // Test/Dogfood/Scenario/Workers.lean, `Observation`. The work left is five entries. The cells
  // are `opened`, `released`, `assigned` and `count`, in allocation order.
  workers: {
    host: ({ exit, ledger }, spelling) => {
      const seen = (call: HeldCall): Json => ({ row: spelling(call), request: call.request, fiber: call.fiber, token: call.token })
      return {
        receipts: ledger.receipts.map(seen),
        applications: ledger.applications.map(seen),
        retired: ledger.retired.map(({ call, kept }) => ({ call: seen(call), kept })),
        rootExit: exit,
        "workLeft.awaiting": ledger.live.map(({ fiber, token, row, request }) => ({ fiber, token, row, request })),
        "workLeft.pending": ledger.stored.map(key)
      }
    },
    through: {
      cells: { fields: ["assignment", "cleanups"], read: ({ cells }) => ({ assignment: entries(cells![2]), cleanups: entries(cells![1]) }) },
      sleeps: { fields: ["workLeft.timers"], read: ({ sleeps }) => ({ "workLeft.timers": sleeps! }) },
      // The count names no fiber. Lean grants the reader only where both of its lists are empty,
      // so zero armed dispatchers is the two empty lists, and any other count is a disagreement.
      dispatchers: { fields: ["workLeft.runnable", "workLeft.queued"], read: ({ armed }) => {
        const none: Json = armed === 0 ? [] : { armed: armed! }
        return { "workLeft.runnable": none, "workLeft.queued": none }
      } }
    }
  },
  // Test/Dogfood/Scenario/Timeout.lean, `Observation`. The cells are `count` and `ended`. Lean
  // grants the sleeps reader in a script where every sleeping fiber is the root or made a call.
  // In any other script the timers wait: a timer's fiber makes no call, so it has no number on
  // the host.
  timeout: {
    host: ({ exit, ledger }, spelling) => ({
      calls: ledger.held.filter(call => spelling(call) === "Http.getQuote").map(call =>
        call.state === "live" ? { live: true }
          : call.state === "retired" ? { retired: call.kept === true }
          : ending(call.reply ?? null, "other")),
      receipts: ledger.receipts.map(key),
      applications: ledger.applications.map(key),
      retired: ledger.retired.map(({ call, kept }) => ({ key: key(call), kept })),
      stored: ledger.stored.map(key),
      root: exit === null ? { running: true } : ending(exit, "interrupted")
    }),
    through: {
      cells: { fields: ["attempts", "cleanups"], read: ({ cells }) => ({ attempts: typeof cells![0] === "number" ? cells![0] : 0, cleanups: entries(cells![1]) }) },
      sleeps: { fields: ["timers"], read: ({ sleeps }) => ({ timers: sleeps!.map(([fiber, wake]) => [fiber, Number(wake)]) }) }
    }
  },
  // Test/Dogfood/Scenario/Atomic.lean, `Observation`. The cells are the window, the account and
  // the cleanup log. The requests 1 to 6 are the fibers 2 to 7: the daemon is fiber 1.
  atomic: {
    host: () => ({}),
    through: {
      cells: { fields: ["window", "account", "cleanups"], read: ({ cells }) => ({ window: cells![0] ?? null, account: cells![1] ?? null, cleanups: entries(cells![2]) }) },
      fibers: { fields: ["decisions", "completed"], read: ({ fibers }) => {
        const decisions = [2, 3, 4, 5, 6, 7].map(fiber => outcome(fibers![fiber]))
        const completed = decisions.filter(decision => decision !== null && typeof decision === "object" &&
          (Object.hasOwn(decision, "admitted") || Object.hasOwn(decision, "failedBehind") || Object.hasOwn(decision, "rejected"))).length
        return { decisions, completed }
      } }
    }
  }
}
/** The entries of a scenario's observation at a script's end, each by its source: measured by
 * the host, predicted by the ledger, measured through a reader that the run has, or waiting.
 * The four sets are the observation. */
export const measure = (fixture: ScenarioFixture, end: HostEnd, readers: Readers): Pick<ScenarioResult, "measured" | "predicted" | "through" | "waits"> => {
  const scenario = scenarios[fixture.scenario]
  if (!scenario) throw Error(`${fixture.name}: the scenario ${fixture.scenario} has no reader`)
  const host = Object.entries(scenario.host(end, call => String((fixture.table[call.row] as { spelling?: unknown }).spelling)))
  const measured = Object.fromEntries(host.filter(([field]) => !scenario.predicted?.includes(field)))
  const predicted = Object.fromEntries(host.filter(([field]) => scenario.predicted?.includes(field)))
  const through: ScenarioResult["through"] = {}, waits: ScenarioResult["waits"] = []
  for (const [reader, { fields, read }] of Object.entries(scenario.through) as Array<[ReaderName, NonNullable<Scenario["through"][ReaderName]>]>) {
    if (readers[reader] === undefined) {
      const refused = fixture.refusedReaders.find(refusal => refusal.reader === reader)
      for (const field of fields) waits.push({ field, why: refused ? `the ${reader} reader is refused: ${refused.why}` : `the run has no ${reader} reader` })
      continue
    }
    const values = read(end)
    for (const field of fields) through[field] = { reader, value: values[field]! }
  }
  const sourced = [...host.map(([field]) => field), ...Object.keys(through), ...waits.map(wait => wait.field)]
  for (const field of Object.keys(fixture.observation)) if (!sourced.includes(field)) waits.push({ field, why: "no reader on the host" })
  const named = [...host.map(([field]) => field), ...Object.keys(through), ...waits.map(wait => wait.field)].sort()
  if (named.join() !== Object.keys(fixture.observation).sort().join())
    throw Error(`${fixture.name}: the readers name ${named.join()} and the observation has ${Object.keys(fixture.observation).sort().join()}`)
  return { measured, predicted, through, waits }
}
