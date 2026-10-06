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
  readers: Readers
  refusedReaders: Array<{ reader: ReaderName; why: string }>
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
