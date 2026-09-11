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
add("control-with-pending", tape => { const i = tape.records.findIndex(r => r.kind === "apply"); tape.records.splice(i, 0, { kind: "flush", version: 2, session: tape.header.session }) }, "two-AB", "same")
add("empty-public-chunk", tape => { tape.records.find(r => r.kind === "reply" && (r.completion as { success: unknown }).success && typeof (r.completion as { success: unknown }).success === "object")!.completion = { success: { some: [] } } }, "stream-3-AB")
const zero = find("two-AB")
controls.push({ name: "zero-application", recording: zero, fuel: 0 }); expectations.push({ name: "zero-application", expected: "zero" })
await writeFile(resolve(directory, "controls.json"), JSON.stringify(controls) + "\n")
await writeFile(resolve(directory, "control-expectations.json"), JSON.stringify(expectations) + "\n")
