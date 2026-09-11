import { deepStrictEqual, notDeepStrictEqual, ok } from "node:assert"
import { readFile, writeFile } from "node:fs/promises"
import { resolve } from "node:path"
import type { Json } from "./protocol.ts"
import { keyText, recordKey, type KeyedRecording } from "./keyed-protocol.ts"
const [runPath, leanPath, controlsPath] = process.argv.slice(2)
if (!runPath || !leanPath || !controlsPath) throw Error("usage: check-keyed.ts RUN LEAN_RESULTS CONTROL_RESULTS")
const read = async <T>(path: string): Promise<T> => JSON.parse(await readFile(path, "utf8")) as T
interface Receipt { status?: string; refused?: string; position?: number; exit?: Json; pending?: number[]; consumed?: number[]; awaits?: unknown[]; oracleAnswers?: number; retired?: number[] }
const hosts = await read<Array<{ name: string; exit: Json }>>(resolve(runPath, "host.json"))
const cases = await read<Array<{ name: string; recording: KeyedRecording }>>(resolve(runPath, "cases.json"))
const lean = await read<Array<{ name: string; result: Receipt }>>(leanPath)
const controlResults = await read<Array<{ name: string; result: Receipt }>>(controlsPath)
const controls = await read<Array<{ name: string; expected: string }>>(resolve(runPath, "control-expectations.json"))
deepStrictEqual(lean.map(x => x.name), cases.map(x => x.name), "every fresh recording is replayed exactly once")
for (const { name, result } of lean) {
  const host = hosts.find(h => h.name === name)!, tape = cases.find(c => c.name === name)!.recording
  deepStrictEqual(result.status, "prefix-end", `${name}: every record accepted`)
  deepStrictEqual(result.position, tape.records.length, `${name}: no silently unconsumed suffix`)
  deepStrictEqual(result.exit, host.exit, `${name}: full ordered exit observation`)
  deepStrictEqual(result.pending, [], `${name}: no pending completion lost at exit`)
  deepStrictEqual(result.awaits, [], `${name}: no outstanding callback`)
  deepStrictEqual(result.oracleAnswers, 0, `${name}: no preloaded answer bypass`)
  const associations = new Map(tape.records.filter(r => r.kind === "call").map(r => [keyText(recordKey(r)), r.callId]))
  const applied = tape.records.filter(r => r.kind === "apply").map(r => associations.get(keyText(recordKey(r))))
  deepStrictEqual(result.consumed, applied, `${name}: exact keyed application sequence`)
  deepStrictEqual(applied.length, associations.size, `${name}: exactly one applied reply per call`)
}
for (const name of ["two", "shared", "kv", "concurrentStreams"]) {
  const ab = lean.find(r => r.name === `${name}-AB`)!.result, ba = lean.find(r => r.name === `${name}-BA`)!.result
  deepStrictEqual(ab, ba, `${name}: independent arrival order with fixed application order`)
}
notDeepStrictEqual(lean.find(r => r.name === "shared-AB")!.result.exit,
  lean.find(r => r.name === "shared-apply-BA")!.result.exit, "resumed shared effects must not be treated as commuting")
deepStrictEqual(controlResults.map(x => x.name), controls.map(x => x.name), "all negative and prefix controls evaluated")
const positive = lean.find(r => r.name === "two-AB")!.result
for (const control of controls) {
  const result = controlResults.find(r => r.name === control.name)!.result
  const refused = result.refused !== undefined || result.status?.startsWith("refused:")
  if (control.expected === "refusal") ok(refused, `${control.name}: mutation must refuse`)
  else {
    ok(!refused, `${control.name}: valid prefix must not refuse`)
    if (control.expected === "different") notDeepStrictEqual(result.exit, positive.exit, "typed payload mutation must affect the compared observation")
    if (control.expected === "same") deepStrictEqual(result.exit, positive.exit)
    if (control.expected === "prefix" || control.expected === "zero") {
      deepStrictEqual(result.exit, null); deepStrictEqual(result.consumed, []); deepStrictEqual(result.awaits?.length, 2)
    }
    if (control.expected === "zero") { deepStrictEqual(result.status, "frontier"); deepStrictEqual(result.pending, [0, 1]) }
  }
}
deepStrictEqual(controlResults.find(r => r.name === "receive-AB")!.result,
  controlResults.find(r => r.name === "receive-BA")!.result, "receipt prefix observation includes canonical pending storage")
const summary = { programs: new Set(cases.map(c => c.recording.header.program)).size, runs: lean.length,
  controls: controls.length, streamPrograms: new Set(cases.filter(c => c.recording.header.program.startsWith("stream-")).map(c => c.recording.header.program)).size,
  observation: "ordered exit reasons and values, exact keyed applications, pending calls and replies, no oracle answers",
  boundary: "finite rc.112 runs; no general host adequacy or application commutation claim" }
await writeFile(resolve(runPath, "checked.json"), JSON.stringify(summary, null, 2) + "\n")
console.log(`PASS keyed differential: ${summary.runs} runs, ${summary.programs} programs, ${summary.controls} controls; exact exits and keyed applications`)
