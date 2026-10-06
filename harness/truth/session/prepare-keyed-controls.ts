/** Mutate freshly recorded evidence, never canned expected host runs. Every refusal is
 * subsequently evaluated by the Lean session as well as the structural boundary. */
import { readFile, writeFile } from "node:fs/promises"
import { resolve } from "node:path"
import type { KeyedRecording, DecisionRecord } from "./keyed-protocol.ts"
const directory = process.argv[2]
if (!directory) throw Error("usage: prepare-keyed-controls.ts RUN_DIRECTORY")
const source = JSON.parse(await readFile(resolve(directory, "cases.json"), "utf8")) as Array<{ name: string; recording: KeyedRecording }>
const find = (name: string) => structuredClone(source.find(x => x.name === name)!.recording)
const controls: Array<{ name: string; recording: KeyedRecording; fuel?: number }> = []
const expectations: Array<{ name: string; expected: "refusal" | "different" | "prefix" | "same" | "zero" }> = []
const add = (name: string, mutate: (tape: KeyedRecording) => void, fixture = "two-AB", expected: typeof expectations[number]["expected"] = "refusal") => {
  const recording = find(fixture); mutate(recording); controls.push({ name, recording }); expectations.push({ name, expected })
}
const row = (tape: KeyedRecording, kind: string): DecisionRecord => tape.records.find(r => r.kind === kind)!
for (const kind of ["call", "reply", "apply"]) for (const field of ["fiber", "token"])
  add(`${kind}-missing-${field}`, tape => { delete row(tape, kind)[field] })
add("wrong-token", tape => { row(tape, "call").token = 91 })
add("wrong-fiber", tape => { row(tape, "call").fiber = 91 })
add("wrong-row", tape => { row(tape, "call").row = 91 })
add("wrong-request", tape => { row(tape, "call").request = 91 })
add("wrong-call-id", tape => { row(tape, "reply").callId = 1 })
add("wrong-session", tape => { row(tape, "reply").session = "foreign" })
add("wrong-version", tape => { (tape.header as { version: number }).version = 1 })
add("legacy-v2", tape => {
  const header = tape.header as { version: number; format: string; profile: string }
  header.version = 2; header.format = "effect4-host-session-v2"; header.profile = "keyed-v2"
})
add("wrong-profile", tape => { (tape.header as { profile: string }).profile = "other" })
add("wrong-table", tape => { (tape.header.table[0] as Record<string, unknown>).trailing = ["extra"] })
add("wrong-answer-type", tape => { row(tape, "reply").completion = { success: "wrong" } })
add("wrong-error-type", tape => { row(tape, "reply").completion = { failure: [{ fail: 7 }] } })
add("extra-field", tape => { row(tape, "reply").extra = true })
add("duplicate-call", tape => { const i = tape.records.findIndex(r => r.kind === "call"); tape.records.splice(i + 1, 0, structuredClone(tape.records[i]!)) })
add("duplicate-reply", tape => { const i = tape.records.findIndex(r => r.kind === "reply"); tape.records.splice(i + 1, 0, structuredClone(tape.records[i]!)) })
add("duplicate-apply", tape => { const i = tape.records.findIndex(r => r.kind === "apply"); tape.records.splice(i + 1, 0, structuredClone(tape.records[i]!)) })
add("late-reply", tape => { tape.records.push(structuredClone(row(tape, "reply"))) })
add("unanswered", tape => { tape.records = tape.records.slice(0, tape.records.findIndex(r => r.kind === "reply")) }, "two-AB", "prefix")
add("receive-AB", tape => { tape.records = tape.records.slice(0, tape.records.findIndex(r => r.kind === "apply")) }, "two-AB", "prefix")
add("receive-BA", tape => { tape.records = tape.records.slice(0, tape.records.findIndex(r => r.kind === "apply")) }, "two-BA", "prefix")
add("wrong-value-same-type", tape => { row(tape, "reply").completion = { success: 99 } }, "two-AB", "different")
add("control-with-pending", tape => { const i = tape.records.findIndex(r => r.kind === "apply"); tape.records.splice(i, 0, { kind: "flush", version: tape.header.version, session: tape.header.session }) }, "two-AB", "same")
add("empty-public-chunk", tape => { tape.records.find(r => r.kind === "reply" && (r.completion as { success: unknown }).success && typeof (r.completion as { success: unknown }).success === "object")!.completion = { success: { some: [] } } }, "stream-3-AB")
const zero = find("two-AB")
controls.push({ name: "zero-application", recording: zero, fuel: 0 }); expectations.push({ name: "zero-application", expected: "zero" })
await writeFile(resolve(directory, "controls.json"), JSON.stringify(controls) + "\n")
await writeFile(resolve(directory, "control-expectations.json"), JSON.stringify(expectations) + "\n")
// The scenarios' recordings (decisions row 254): the red controls of Lean's replay. Each is a
// recording of the host with one moved record. Lean's replay must show another observation, or
// give a record another verdict than the ledger predicted.
//  - In one recording of each scenario the first reply application moves before its reply
//    receipt. Where no script of a scenario applies a reply, the second record moves before the
//    first.
//  - In each recording with a late reply, a reply that the recorder's ledger predicted as
//    `noCall`, that reply moves to stand right after its call, where the call is still live.
const scenarios = await readFile(resolve(directory, "scenario-cases.json"), "utf8").then(
  text => JSON.parse(text) as Array<{ name: string; recording: KeyedRecording }>, () => undefined)
if (scenarios) {
  const hosts = JSON.parse(await readFile(resolve(directory, "scenario-host.json"), "utf8")) as
    Array<{ name: string; predictions: Array<{ at: number; row: string; reason: string }> }>
  // A moved record keeps the ledger's prediction: each prediction is indexed again.
  const moved: Array<{ name: string; recording: KeyedRecording; predictions: typeof hosts[number]["predictions"] }> = []
  const move = (name: string, recording: KeyedRecording, from: number, to: number): void => {
    const [record] = recording.records.splice(from, 1)
    recording.records.splice(to, 0, record!)
    const predictions = hosts.find(host => host.name === name)!.predictions.map(prediction =>
      ({ ...prediction, at: prediction.at === from ? to : prediction.at >= to && prediction.at < from ? prediction.at + 1 : prediction.at }))
    moved.push({ name, recording, predictions })
  }
  for (const scenario of new Set(scenarios.map(run => run.name.split("/")[0]!))) {
    const runs = scenarios.filter(run => run.name.startsWith(`${scenario}/`))
    const { name, recording } = structuredClone(runs.find(run => run.recording.records.some(record => record.kind === "apply")) ?? runs[0]!)
    const apply = recording.records.findIndex(record => record.kind === "apply")
    move(name, recording, apply > 0 ? apply : 1, apply > 0 ? apply - 1 : 0)
  }
  for (const { name, predictions } of hosts) {
    const late = predictions.find(prediction => prediction.row === "submit" && prediction.reason === "noCall")
    if (!late) continue
    const recording = structuredClone(scenarios.find(run => run.name === name)!.recording), reply = recording.records[late.at]!
    const call = recording.records.findIndex(record => record.kind === "call" && record.fiber === reply.fiber && record.token === reply.token)
    if (call < 0) throw Error(`${name}: a late reply has no call record`)
    move(name, recording, late.at, call + 1)
  }
  await writeFile(resolve(directory, "scenario-controls.json"), JSON.stringify(moved) + "\n")
}
