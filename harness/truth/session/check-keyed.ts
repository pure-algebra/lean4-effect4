import { AssertionError, deepStrictEqual, notDeepStrictEqual, ok, throws } from "node:assert"
import { readFile, writeFile } from "node:fs/promises"
import { resolve } from "node:path"
import type { Json } from "./protocol.ts"
import { keyText, recordKey, type KeyedRecording } from "./keyed-protocol.ts"
import type { ScenarioFixture, ScenarioManifest, ScenarioResult } from "./keyed-observation.ts"
const [runPath, leanPath, controlsPath, scenariosPath, scenarioLeanPath, scenarioControlsPath] = process.argv.slice(2)
if (!runPath || !leanPath || !controlsPath) throw Error("usage: check-keyed.ts RUN LEAN_RESULTS CONTROL_RESULTS [SCENARIOS SCENARIO_RESULTS SCENARIO_CONTROL_RESULTS]")
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

// ---- the scenarios' host runs (decisions row 254) ----------------------------------------
if (scenariosPath && scenarioLeanPath && scenarioControlsPath) {
  /** Lean's replay of one recording (`Keyed.lean`, `replayRun`). */
  interface Replay { refused?: string; same?: boolean; fields?: Record<string, boolean>; verdicts?: Array<string | { refused: string }> }
  type Replays = Array<{ name: string; result: Replay }>
  type Cases = Array<{ name: string; recording: KeyedRecording }>
  const manifest = await read<ScenarioManifest>(scenariosPath)
  const hosts = await read<ScenarioResult[]>(resolve(runPath, "scenario-host.json"))
  const faulty = await read<Array<ScenarioResult & { fault: string; field: string }>>(resolve(runPath, "scenario-faults.json"))
  const plain = await read<Cases>(resolve(runPath, "scenario-cases.json"))
  const withReaders = await read<Cases>(resolve(runPath, "scenario-reader-cases.json"))
  const aloneCases = await read<Array<Cases[number] & { reader: string }>>(resolve(runPath, "scenario-alone-cases.json"))
  const replays = await read<Replays>(scenarioLeanPath)
  const moved = await read<Replays>(scenarioControlsPath)
  const movedCases = await read<Array<{ name: string; predictions: ScenarioResult["predictions"] }>>(resolve(runPath, "scenario-controls.json"))
  const fixtureOf = (name: string): ScenarioFixture => manifest.runs.find(run => run.name === name)!
  const byName = <T extends { name: string }>(list: T[], name: string): T => list.find(item => item.name === name)!
  /** The host's part of one run's comparison. Each entry that the host measured, by itself or
   * through a reader, is the same entry of the script's observation on the Lean machine. So is
   * each entry that the recorder's ledger predicted. The message names the run, the entry and
   * its source of evidence. */
  const compareHost = (fixture: ScenarioFixture, host: ScenarioResult): void => {
    for (const [field, value] of Object.entries(host.measured))
      deepStrictEqual(value, fixture.observation[field], `${fixture.name}: the host's ${field} is not the Lean machine's`)
    for (const [field, value] of Object.entries(host.predicted))
      deepStrictEqual(value, fixture.observation[field], `${fixture.name}: the ledger's ${field} is not the Lean machine's`)
    for (const [field, { reader, value }] of Object.entries(host.through))
      deepStrictEqual(value, fixture.observation[field], `${fixture.name}: the host's ${field}, through the ${reader} reader, is not the Lean machine's`)
  }
  /** The replay's part. Lean's replay of the recording shows the script's whole observation,
   * field for field. It is replay evidence: it measures nothing more of the host. */
  const compareReplay = (name: string, replay: Replay): void => {
    ok(replay.refused === undefined, `${name}: Lean refuses the recording (${replay.refused})`)
    for (const [field, same] of Object.entries(replay.fields ?? {})) ok(same, `${name}: Lean's replay shows another ${field}`)
    ok(replay.same === true, `${name}: Lean's replay shows another observation`)
  }
  /** The recorder's ledger is no second session. Each refusal that it predicted is the verdict
   * that Lean's session gives the same record, and the session refuses no other record. */
  const comparePredictions = (name: string, host: Pick<ScenarioResult, "predictions">, replay: Replay): void => {
    const predicted = (replay.verdicts ?? []).map((_, at) => host.predictions.find(prediction => prediction.at === at)?.reason ?? null)
    const refused = (replay.verdicts ?? []).map(verdict => typeof verdict === "string" ? null : verdict.refused)
    deepStrictEqual(predicted, refused, `${name}: the recorder's predictions are not the session's verdicts`)
  }
  /** The readers' control, in three parts.
   *  - The run with its readers and the exact wait leaves the recording of the plain run, byte
   *    for byte, the same entries where the plain run gives one, and the same exit of the root.
   *  - A run with one reader alone, under the plain run's scheduler and wait, leaves that
   *    recording and that exit too.
   *  - What a reader gives alone is what it gives among the other readers and the exact wait.
   * A script with no call has a recording of its controls alone. The root's exit and the third
   * part are what sees such a program. A reader's effect on its own entries has no control:
   * no run without the reader reads them. */
  const sameRecording = (name: string, what: string, without: KeyedRecording, withThem: KeyedRecording): void => {
    const left = JSON.stringify(without), right = JSON.stringify(withThem)
    if (left === right) return
    const at = without.records.findIndex((record, index) => JSON.stringify(record) !== JSON.stringify(withThem.records[index]))
    throw new AssertionError({ message: `${name}: ${what} the recording at record ${at < 0 ? without.records.length : at}`, actual: right, expected: left })
  }
  const compareReaders = (name: string, host: ScenarioResult, without: KeyedRecording, withThem: KeyedRecording, only: typeof aloneCases): void => {
    sameRecording(name, "the readers change", without, withThem)
    deepStrictEqual(host.withReaders, { ...host.measured, ...host.predicted }, `${name}: the readers change an entry that the plain run gives`)
    deepStrictEqual(host.rootExits[1], host.rootExits[0], `${name}: the readers change the root's exit`)
    deepStrictEqual(only.map(run => run.reader).sort(), Object.keys(host.alone).sort(), `${name}: each reader has its run alone`)
    for (const run of only) sameRecording(name, `the ${run.reader} reader alone changes`, without, run.recording)
    for (const [reader, { rootExit, entries }] of Object.entries(host.alone)) {
      deepStrictEqual(rootExit, host.rootExits[0], `${name}: the ${reader} reader alone changes the root's exit`)
      for (const [field, value] of Object.entries(entries))
        deepStrictEqual(value, host.through[field]?.value, `${name}: the ${reader} reader gives another ${field} alone than among the other readers`)
    }
  }
  deepStrictEqual(hosts.map(run => run.name), manifest.runs.map(run => run.name), "every script that a host can perform is performed once")
  deepStrictEqual(replays.map(run => run.name), hosts.map(run => run.name), "every recording of a script is replayed once")
  for (const host of hosts) {
    const replay = byName(replays, host.name).result
    compareHost(fixtureOf(host.name), host)
    compareReplay(host.name, replay)
    comparePredictions(host.name, host, replay)
    compareReaders(host.name, host, byName(plain, host.name).recording, byName(withReaders, host.name).recording,
      aloneCases.filter(run => run.name === host.name))
  }
  const named = (name: string, field: string) => (error: unknown): boolean =>
    error instanceof AssertionError && error.message.startsWith(`${name}: `) && error.message.includes(field)
  // Red control of the comparator: one changed expectation fails by the run's name, at the entry.
  const scenarioNames = [...new Set(hosts.map(run => run.scenario))]
  const changed: string[] = []
  for (const scenario of scenarioNames) {
    const host = hosts.find(run => run.scenario === scenario)!
    const fixture = structuredClone(fixtureOf(host.name)), field = [...Object.keys(host.measured), ...Object.keys(host.predicted), ...Object.keys(host.through)][0]!
    fixture.observation[field] = { changed: fixture.observation[field]! }
    throws(() => compareHost(fixture, host), named(host.name, field), `${host.name}: a changed expectation must fail the comparison`)
    changed.push(`${host.name}: ${field}`)
  }
  // Red control of the host's measurement: a fault on the host only. It keeps every other
  // entry, the root's exit among them, and the comparison fails at the faulty entry. The fault
  // is a dropped assignment of the workers scenario, so the control stands with that scenario.
  if (scenarioNames.includes("workers")) ok(faulty.length > 0, "the host's measurement has its red control")
  for (const host of faulty) {
    const fixture = fixtureOf(host.name)
    const { [host.field]: _through, ...through } = host.through, { [host.field]: _measured, ...measured } = host.measured
    ok(Object.hasOwn(host.through, host.field) || Object.hasOwn(host.measured, host.field), `${host.name}: the fault ${host.fault} names a measured entry`)
    compareHost(fixture, { ...host, measured, through })
    throws(() => compareHost(fixture, host), named(host.name, host.field), `${host.name}: the fault ${host.fault} must fail at ${host.field}`)
  }
  // Red control of Lean's replay: a recording with one moved record does not replay as the
  // script. Lean shows another observation, or its session gives a record another verdict than
  // the ledger predicted. A moved late reply is one of them, where a script has a late reply.
  deepStrictEqual(moved.map(run => run.name), movedCases.map(run => run.name), "every moved recording is replayed once")
  moved.forEach(({ name, result }, index) =>
    throws(() => { compareReplay(name, result); comparePredictions(name, movedCases[index]!, result) }, named(name, ""),
      `${name}: a recording with a moved record must not replay as the script`))
  // Red control of a reader's premise. Lean refuses the fibers reader to a program that holds a
  // race, so the timeout scenario cannot use it. A granted reader is one whose premise holds.
  const racing = manifest.runs.filter(run => run.scenario === "timeout")
  for (const run of racing)
    ok(typeof run.premises.fibers === "string" && run.premises.fibers.includes("race") && run.readers.fibers === undefined,
      `${run.name}: the fibers reader must be refused to a program that holds a race`)
  for (const run of manifest.runs) for (const reader of Object.keys(run.readers) as Array<keyof typeof run.readers>)
    ok(run.premises[reader] === true, `${run.name}: the ${reader} reader is on, and its premise fails`)
  // Red control of the readers' control: one dropped record of a recording is a difference.
  const dropped: string[] = []
  for (const scenario of scenarioNames) {
    const host = hosts.find(run => run.scenario === scenario)!, recording = byName(plain, host.name).recording
    throws(() => compareReaders(host.name, host, recording, { ...recording, records: recording.records.slice(0, -1) }, []), named(host.name, "the readers change the recording"))
    dropped.push(host.name)
  }
  // Red control of the predictions: one prediction taken away is a difference, where a script
  // has a refused record.
  const unpredicted: string[] = []
  for (const host of hosts.filter(run => run.predictions.length > 0)) {
    throws(() => comparePredictions(host.name, { ...host, predictions: host.predictions.slice(1) }, byName(replays, host.name).result), named(host.name, "predictions"))
    unpredicted.push(host.name)
  }
  // Each entry's evidence, by scenario: measured by the host, predicted by the ledger, measured
  // through a named reader, or replay only. An entry may have a reader in some scripts and wait
  // in the others. The table goes to `scenario-evidence.md`, so that no document counts by hand.
  const scenarios = scenarioNames.map(scenario => {
    const runs = hosts.filter(run => run.scenario === scenario)
    const evidence = fixtureOf(runs[0]!.name).fields.flatMap(entry => {
      const words = runs.map(run => Object.hasOwn(run.measured, entry) ? "host" : Object.hasOwn(run.predicted, entry) ? "ledger"
        : run.through[entry] ? `reader: ${run.through[entry]!.reader}` : "replay only")
      return [...new Set(words)].map(word => ({ entry, evidence: word, scripts: runs.filter((_, index) => words[index] === word).map(run => run.name) }))
    })
    return { scenario, scripts: runs.length, evidence, wholeObservationOnHost: !evidence.some(row => row.evidence === "replay only") }
  })
  const controls = { comparator: changed, hostMeasurement: faulty.map(host => `${host.name}: ${host.fault}, at ${host.field}`),
    replay: moved.map(run => run.name), readers: dropped, predictions: unpredicted,
    premises: racing.map(run => `${run.name}: no fibers reader`) }
  const versions = await read<{ effect: string; bun: string }>(resolve(runPath, "versions.json"))
  await writeFile(resolve(runPath, "scenario-checked.json"), JSON.stringify({ host: versions, scenarios, notPerformed: manifest.waiting, controls,
    evidence: "each run is a finite host run of one script on rc.112; an entry is measured by the host, predicted by the ledger, measured through a reader, or replay only",
    boundary: "no agreement for another script or another entry; no host adequacy; no liveness" }, null, 2) + "\n")
  // An entry with two sources has two rows, each with its scripts by name.
  const scriptsOf = (scenario: string, scripts: number, names: string[]): string =>
    names.length === scripts ? `all ${scripts}` : `${names.length} of ${scripts}: ${names.map(name => name.slice(scenario.length + 1)).join(", ")}`
  await writeFile(resolve(runPath, "scenario-evidence.md"), [
    "| Scenario | Entry | Evidence | Scripts |", "| --- | --- | --- | --- |",
    ...scenarios.flatMap(({ scenario, scripts, evidence }) => evidence.map(row =>
      `| ${scenario} | \`${row.entry}\` | ${row.evidence} | ${scriptsOf(scenario, scripts, row.scripts)} |`)),
    ""].join("\n"))
  // The acceptance line of each scenario: how many entries have each source in every script,
  // and, for each entry that waits, the scripts where the whole-observation comparison waits,
  // by count and by name.
  const line = scenarios.map(({ scenario, scripts, evidence }) => {
    const whole = (word: (evidence: string) => boolean): number => evidence.filter(row => word(row.evidence) && row.scripts.length === scripts).length
    const waits = evidence.filter(row => row.evidence === "replay only")
    const parts = [`${whole(word => word === "host")} entries measured by the host`,
      ...(whole(word => word === "ledger") ? [`${whole(word => word === "ledger")} predicted by the ledger`] : []),
      ...(whole(word => word.startsWith("reader")) ? [`${whole(word => word.startsWith("reader"))} through a reader`] : []),
      ...evidence.filter(row => row.evidence.startsWith("reader") && row.scripts.length < scripts).map(row => `${row.entry} through a reader in ${row.scripts.length} scripts`)]
    const short = (names: string[]): string => names.map(name => name.slice(scenario.length + 1)).join(", ")
    const waiting = waits.length
      ? `the whole-observation comparison waits on ${waits.map(row => `${row.entry} in ${row.scripts.length} scripts (${short(row.scripts)})`).join(", ")}`
      : "no entry waits"
    return `${scenario} ${scripts} scripts (${parts.join(", ")}; ${waiting})`
  }).join("; ")
  const count = Object.values(controls).reduce((sum, list) => sum + list.length, 0)
  console.log(`PASS keyed scenarios on effect ${versions.effect} under bun ${versions.bun}: ${line}; ${manifest.waiting.length} scripts with no host run; ${count} red controls`)
}
