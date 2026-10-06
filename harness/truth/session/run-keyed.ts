/** Run the exact Lean-printed expressions, then save fresh v3 tapes and host receipts.
 * Binding plans are explicit before execution; none of their completions executes on host.
 *
 * With a third argument the runner then performs the scenarios' scripts (decisions row 254):
 * each printed module, verbatim, under the same recorder and the same clock boundary. An act
 * of a script is one row of the script's journal. The runner performs each script twice. The
 * plain run has no reader, the pinned default scheduler and a fixed wait. The other run has the
 * readers that Lean grants it, and it waits until no dispatcher is armed. The runner writes both
 * recordings, and beside them what the host measured of the scenario's observation. */
import { mkdir, readFile, writeFile } from "node:fs/promises"
import { dirname, relative, resolve } from "node:path"
import { pathToFileURL } from "node:url"
import { setImmediate } from "node:timers/promises"
import { deepStrictEqual } from "node:assert"
import { Effect, Ref, type Exit, type Fiber } from "effect"
import * as Prelude from "../prelude.ts"
import { KeyedRecorder, exitJson, valueJson, type KeyedFixture } from "./keyed-recorder.ts"
import { ArmedDispatchers, KeyedBindings, ScriptedHost, bindScenario, declareScenario } from "./keyed-bindings.ts"
import { measure, type HostEnd, type Readers, type ScenarioFixture, type ScenarioManifest, type ScenarioResult } from "./keyed-observation.ts"
import type { KeyedRecording } from "./keyed-protocol.ts"
import type { Json } from "./protocol.ts"
import { Rc112ClockBoundary } from "./clock.ts"
const [manifestPath, outputPath, scenariosPath] = process.argv.slice(2)
if (!manifestPath || !outputPath) throw Error("usage: run-keyed.ts LEAN_FIXTURES OUTPUT_DIRECTORY [SCENARIO_FIXTURES]")
const fixtures = JSON.parse(await readFile(manifestPath, "utf8")) as KeyedFixture[]
const output = resolve(outputPath)
await mkdir(output, { recursive: true })
// The `effect` that a written module loads is the one that bun resolves from the output folder.
// It must be the runner's own, the pinned package: in a folder with no `node_modules` above it,
// bun takes a newer build from its cache, and the two builds then run one fiber together.
const pinned = Bun.resolveSync("effect", import.meta.dir)
if (Bun.resolveSync("effect", output) !== pinned)
  throw Error(`the output folder resolves effect to ${Bun.resolveSync("effect", output)}, and the runner loads ${pinned}`)
const versions = { effect: (JSON.parse(await readFile(resolve(dirname(pinned), "../package.json"), "utf8")) as { version: string }).version, bun: Bun.version }
await writeFile(resolve(output, "versions.json"), JSON.stringify(versions) + "\n")
console.log(`keyed host: effect ${versions.effect} under bun ${versions.bun}, loaded from ${dirname(dirname(pinned))}`)
const receipts = []
const cases = []
for (const fixture of fixtures) {
  const modulePath = resolve(output, `${fixture.name}.ts`)
  const bindingsImport = "./" + relative(dirname(modulePath), resolve(import.meta.dir, "keyed-bindings.ts"))
  const preludeImport = "./" + relative(dirname(modulePath), resolve(import.meta.dir, "../prelude.ts"))
  await writeFile(modulePath, `// Generated from the admitted Lean fixture; do not edit.\nimport { Effect, Fiber, Ref } from "effect"\nimport { pair } from ${JSON.stringify(preludeImport)}\nimport type { KeyedBindings } from ${JSON.stringify(bindingsImport)}\nexport const build = ({Host, Kv}: KeyedBindings) => ${fixture.expression}\n`)
  const { build } = await import(pathToFileURL(modulePath).href) as { build: (binding: KeyedBindings) => Effect.Effect<unknown, unknown> }
  for (const order of ["AB", ...(fixture.name.startsWith("stream-") ? [] : ["BA"]), ...(fixture.name === "shared" ? ["apply-BA"] : [])]) {
    const reversed = order === "BA"
    const name = `${fixture.name}-${order}`
    const recorder = new KeyedRecorder(fixture, name), binding = new KeyedBindings(recorder)
    let completed: Exit.Exit<unknown, unknown> | undefined
    const clock = await Rc112ClockBoundary.make()
    const fiber = Effect.runFork(clock.provide(build(binding)))
    fiber.addObserver(exit => { completed = exit })
    try {
      const started = Date.now()
      while (!completed) {
        clock.check()
        if (Date.now() - started > 8000) throw Error(`${name}: host frontier timed out`)
        await setImmediate()
        const open = recorder.outstanding()
        const next = order === "apply-BA" ? open.at(-1) : open[0]
        if (!next) continue
        // Fresh allocations are prepared individually; independent scalar/read/pull replies
        // may arrive in either order. Application always follows the fixed plan.
        const allocation = fixture.name === "kv" || fixture.name === "concurrentStreams" || fixture.name.startsWith("stream-")
        const arrivals = allocation && next.row === 0 ? [next] : open.filter(c => !(allocation && c.row === 0))
        if (reversed) arrivals.reverse()
        for (const call of arrivals) if (!recorder.hasReply(call)) await recorder.arrive(call)
        recorder.apply(next)
      }
      clock.check()
      const observed = exitJson(completed)
      deepStrictEqual(observed, order === "apply-BA" ? { success: 1 } : fixture.expected, `${name}: actual rc.112 exit versus finite Lean model`)
      clock.check()
      const recording = recorder.finish()
      for (const resource of binding.resources) {
        deepStrictEqual([resource.closed, resource.closes], [true, 1], `${name}: exactly one close`)
      }
      const recordPath = resolve(output, `${name}.json`)
      await writeFile(recordPath, JSON.stringify(recording, null, 2) + "\n")
      cases.push({ name, recording })
      receipts.push({ name, exit: observed, associations: recorder.associations(), resources: binding.snapshot(), records: recording.records.length })
    } finally {
      fiber.interruptUnsafe()
      await binding.dispose()
      await clock.dispose()
    }
  }
}
await writeFile(resolve(output, "cases.json"), JSON.stringify(cases) + "\n")
await writeFile(resolve(output, "host.json"), JSON.stringify(receipts, null, 2) + "\n")
console.log(`PASS keyed host: ${receipts.length} actual rc.112 runs; ${fixtures.length} admitted printed programs`)

// ---- the scenarios' scripts (decisions row 254) ------------------------------------------
if (scenariosPath) {
  const manifest = JSON.parse(await readFile(scenariosPath, "utf8")) as ScenarioManifest
  type Variant = "plain" | "readers" | "drops-assignment"
  /** The printed module, verbatim, under a header. The plain header is the truth lane's
   * (`../run-truth.ts`, `importHeader`): the names of the pinned `effect` that a printed module
   * may mention, then the prelude. It takes every value that the prelude exports, and the
   * prelude's type aliases that a printed annotation names. Then it binds the rows of the
   * scenario's table as the objects that the module names. A run with the cells reader or the
   * fibers reader has one more header: it binds `Ref` or `Effect` to the reader's object, which
   * inherits from the pinned one. The module's text under the header is the same bytes. */
  const preludeTypes = ["MaskRestore"]
  const header = (fixture: ScenarioFixture, variant: Variant, modulePath: string): string => {
    const from = (file: string): string => JSON.stringify("./" + relative(dirname(modulePath), resolve(import.meta.dir, file)))
    const name = JSON.stringify(fixture.name)
    const cells = variant !== "plain" && fixture.readers.cells !== undefined
    const fibers = variant !== "plain" && fixture.readers.fibers !== undefined
    const pinned = ["Cause", "Context", "Data", "Deferred", fibers ? "Effect as PinnedEffect" : "Effect", "Exit", "Fiber", "Layer", "Option", cells ? "Ref as PinnedRef" : "Ref", "Scope", "pipe"]
    const prelude = [...Object.keys(Prelude).filter(value => !fixture.namespaces.includes(value)), ...preludeTypes.map(type => `type ${type}`)]
    const bound = [...(fibers ? ["scenarioEffect"] : []), ...(cells ? ["scenarioRef"] : []), "scenarioRows"]
    return [
      "// Generated from the admitted Lean fixture; do not edit.",
      `import { ${pinned.join(", ")} } from "effect"`,
      `import { ${prelude.join(", ")} } from ${from("../prelude.ts")}`,
      `import { ${bound.join(", ")} } from ${from("keyed-bindings.ts")}`,
      ...(fibers ? [`const Effect = scenarioEffect(${name})`, "namespace Effect { export type Effect<A, E = never, R = never> = PinnedEffect.Effect<A, E, R> }"] : []),
      ...(cells ? [`const Ref = scenarioRef(${name}${variant === "drops-assignment" ? `, "drops-assignment"` : ""})`, "namespace Ref { export type Ref<A> = PinnedRef.Ref<A> }"] : []),
      ...(fixture.namespaces.length ? [`const { ${fixture.namespaces.join(", ")} } = scenarioRows<${fixture.bindings}>(${name})`] : []),
      ""
    ].join("\n")
  }
  const modules = new Map<string, Effect.Effect<unknown, unknown>>()
  /** One module a header: the plain module serves a run whose readers change no header. */
  const moduleOf = async (fixture: ScenarioFixture, variant: Variant): Promise<Effect.Effect<unknown, unknown>> => {
    const file = fixture.name.replaceAll("/", "-")
    const plainPath = resolve(output, `${file}.ts`), plain = header(fixture, "plain", plainPath)
    const variantPath = resolve(output, `${file}.${variant}.ts`)
    const own = variant !== "plain" && header(fixture, variant, plainPath) !== plain
    const modulePath = own ? variantPath : plainPath
    let main = modules.get(modulePath)
    if (!main) {
      await writeFile(modulePath, header(fixture, own ? variant : "plain", modulePath) + fixture.module)
      declareScenario(fixture.name, fixture.table)
      main = (await import(pathToFileURL(modulePath).href) as { main: Effect.Effect<unknown, unknown> }).main
      modules.set(modulePath, main)
    }
    return main
  }
  /** The plain run's wait: rc.112 runs a dispatcher's tasks in one macrotask, and a task may arm
   * another dispatcher, so the plain run waits a fixed number of turns. It is the reference of
   * the readers' control: the run with the exact wait must leave the same recording. */
  const turns = async (): Promise<void> => { for (let turn = 0; turn < 64; turn++) await setImmediate() }
  /** Perform one script: act out each row, then read what the host holds at the script's end. */
  const perform = async (fixture: ScenarioFixture, variant: Variant): Promise<{ recording: KeyedRecording; result: Pick<ScenarioResult, "measured" | "predicted" | "through" | "waits" | "predictions"> }> => {
    const readers: Readers = variant === "plain" ? {} : fixture.readers
    const main = await moduleOf(fixture, variant)
    const view: KeyedFixture = { name: fixture.name, expression: "", table: fixture.table, source: null,
      plan: fixture.calls.map((call, callId) => ({ ...call, callId })), expected: null, scripted: true }
    const recorder = new KeyedRecorder(view, fixture.session), host = new ScriptedHost(recorder)
    const clock = await Rc112ClockBoundary.make()
    if (readers.sleeps) clock.noteSleeps()
    const dispatchers = variant === "plain" ? undefined : new ArmedDispatchers()
    const settle = dispatchers ? (): Promise<void> => dispatchers.idle() : turns
    let root: Fiber.Fiber<unknown, unknown> | undefined, exit: Exit.Exit<unknown, unknown> | undefined
    bindScenario(fixture.name, host)
    try {
      for (const act of fixture.acts) {
        clock.check()
        switch (act.kind) {
          // The recorder wrote the root's evaluation when it was made. rc.112 runs the root at
          // once, to its first suspension, and no dispatcher runs before the next act.
          case "evaluate": {
            if (root || act.fiber !== 0) throw Error(`${fixture.name}: only the root starts, and once`)
            root = Effect.runFork(clock.provide(main), dispatchers ? { scheduler: dispatchers.scheduler } : undefined)
            recorder.attachRoot(root)
            root.addObserver(result => { exit = result })
            break
          }
          case "flush": recorder.flush(); await settle(); break
          case "advanceClock": await recorder.advanceClock(clock, act.millis); await settle(); break
          case "cancel": recorder.cancel(act.fiber); await settle(); break
          case "call": recorder.hold(act); break
          case "reply": host.stage(act.completion); await recorder.arrive(act); break
          case "apply": recorder.apply(act); await settle(); break
        }
      }
      clock.check()
      if (!root) throw Error(`${fixture.name}: the script never starts the root`)
      // A reader refuses where its premise fails: the count that Lean found is the count here.
      const refuse = (reader: string, why: string): never => { throw Error(`${fixture.name}: the ${reader} reader is refused: ${why}`) }
      if (readers.cells !== undefined && host.cells.length !== readers.cells)
        refuse("cells", `the module made ${host.cells.length} cells, and the machine holds ${readers.cells}`)
      if (readers.fibers !== undefined && host.forks.length !== readers.fibers)
        refuse("fibers", `the module forked ${host.forks.length} fibers, and the machine holds ${readers.fibers}`)
      const exitOf = (found: Exit.Exit<unknown, unknown> | undefined): Json => found === undefined ? null : recorder.exitOf(found, readers.fibers !== undefined ? host.forks : [])
      const end: HostEnd = {
        exit: exitOf(exit),
        ledger: recorder.measurements(),
        ...(readers.cells !== undefined ? { cells: host.cells.map(cell => valueJson(Ref.getUnsafe(cell))) } : {}),
        ...(readers.fibers !== undefined ? { fibers: [exitOf(exit), ...host.forks.map(fork => exitOf(fork.pollUnsafe()))] } : {}),
        ...(readers.sleeps ? { sleeps: clock.sleeps().map(({ fiber, wake }): [number, string] =>
          [recorder.fiberOf(fiber) ?? refuse("sleeps", "a sleeping fiber has no number on the host"), wake.toString()]) } : {}),
        ...(readers.dispatchers ? { armed: dispatchers!.armed() } : {})
      }
      const result = { ...measure(fixture, end, readers), predictions: end.ledger.refusals }
      return { recording: recorder.snapshot(), result }
    } finally {
      bindScenario(fixture.name, undefined)
      root?.interruptUnsafe()
      await clock.dispose()
    }
  }
  const plainCases: Array<{ name: string; recording: KeyedRecording }> = []
  const readerCases: typeof plainCases = []
  const results: ScenarioResult[] = []
  for (const fixture of manifest.runs) {
    const plain = await perform(fixture, "plain"), read = await perform(fixture, "readers")
    await writeFile(resolve(output, `${fixture.name.replaceAll("/", "-")}.json`), JSON.stringify(plain.recording, null, 2) + "\n")
    plainCases.push({ name: fixture.name, recording: plain.recording })
    readerCases.push({ name: fixture.name, recording: read.recording })
    results.push({ name: fixture.name, scenario: fixture.scenario, measured: plain.result.measured, predicted: plain.result.predicted,
      through: read.result.through, waits: read.result.waits, withReaders: { ...read.result.measured, ...read.result.predicted },
      predictions: plain.result.predictions, records: plain.recording.records.length })
  }
  // The red control of the host's measurement: a fault on the host only. The faulty host's `Ref`
  // drops one update of the cell `assigned`. The root's exit does not read that cell.
  const faults: Array<ScenarioResult & { fault: string; field: string }> = []
  for (const { run, fault, field } of [{ run: "workers/lowest", fault: "drops-assignment", field: "assignment" }] as const) {
    const fixture = manifest.runs.find(candidate => candidate.name === run)
    if (!fixture || fixture.readers.cells === undefined) continue
    const { recording, result } = await perform(fixture, fault)
    faults.push({ name: run, scenario: fixture.scenario, measured: result.measured, predicted: result.predicted, through: result.through,
      waits: result.waits, withReaders: { ...result.measured, ...result.predicted }, predictions: result.predictions,
      records: recording.records.length, fault, field })
  }
  await writeFile(resolve(output, "scenario-cases.json"), JSON.stringify(plainCases) + "\n")
  await writeFile(resolve(output, "scenario-reader-cases.json"), JSON.stringify(readerCases) + "\n")
  await writeFile(resolve(output, "scenario-host.json"), JSON.stringify(results, null, 2) + "\n")
  await writeFile(resolve(output, "scenario-faults.json"), JSON.stringify(faults, null, 2) + "\n")
  console.log(`PASS keyed scenarios: ${results.length} scripts performed on actual rc.112, each with no reader and with its readers; ${manifest.waiting.length} scripts with no host run`)
}
