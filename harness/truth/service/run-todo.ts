/** The to-do's scripts on its emitted Effect service, under rc.112 (decisions row 378 (20), slice E4).
 *
 * The keyed lane writes one fixture for each script of the to-do's battery that a host can
 * perform (`Keyed.lean scenarios`). This runner performs each one with the lane's recorder and
 * host (`KeyedRecorder`, `ScriptedHost`, `provideScenario`), as `run-keyed.ts` performs it, with
 * one change. The root is no printed request module: it is the consumer's program
 * (`consumer.ts`), which takes the service by its key, calls the method of the script and provides
 * the service's layer. The repository is the scenario's rows, provided under the module's own key
 * (`provideScenario`), and each answer of it is the script's completion: a tape.
 *
 * The runner compares what the host measures with Lean's observation of the script, and writes
 * each recording. Lean then replays each recording against the script's program
 * (`Keyed.lean scenario-batch`) and decides the per-run checks (`Keyed.lean service-checks`).
 *
 *     bun --no-install harness/truth/service/run-todo.ts SCENARIOS OUT
 *
 * `SCENARIOS` is `Keyed.lean scenarios`' output. The emitted module stands in the keyed lane's
 * work folder (`EmitTodo.lean`). */
import { readFile, writeFile, mkdir } from "node:fs/promises"
import { resolve } from "node:path"
import { setImmediate } from "node:timers/promises"
import { AssertionError, deepStrictEqual, throws } from "node:assert"
import { Effect, type Exit, type Fiber } from "effect"
import { KeyedRecorder, type KeyedFixture } from "../session/keyed-recorder.ts"
import { ScriptedHost, bindScenario, declareScenario, provideScenario } from "../session/keyed-bindings.ts"
import { measure, type HostEnd, type ScenarioFixture, type ScenarioManifest } from "../session/keyed-observation.ts"
import type { KeyedRecording } from "../session/keyed-protocol.ts"
import type { Json } from "../session/protocol.ts"
import { Rc112ClockBoundary } from "../session/clock.ts"
import * as Service from "../session/.work/service/todo.gen.ts"
import { programs } from "./consumer.ts"

const [scenariosPath, outPath] = process.argv.slice(2)
if (!scenariosPath || !outPath) throw Error("usage: run-todo.ts SCENARIOS OUT")
const effect = (JSON.parse(await readFile(resolve(import.meta.dir, "../node_modules/effect/package.json"), "utf8")) as { version: string }).version
if (effect !== "4.0.0-rc.112") throw Error(`the pinned effect 4.0.0-rc.112 is required, and ${effect} loaded`)
console.log(`effect ${effect} under bun ${Bun.version}`)

/** The consumer's program of each script of the to-do's battery, by the script's name. A script
 * that opens a built entry runs that entry's method at the script's argument (`runsOf`,
 * `Test/Dogfood/Scenario/Todo/Claims.lean`). */
const programOf: Record<string, Effect.Effect<unknown, unknown, unknown>> = {
  "todo/empty": programs.addEmpty, "todo/milk": programs.addMilk,
  "todo/locked": programs.completeOne, "todo/other-tag": programs.completeOne,
  "todo/done": programs.completeOne, "todo/other-todo": programs.completeOne,
  "todo/wide": programs.completeOne,
  "todo/model-add": programs.addMilk, "todo/model-list": programs.list,
  "todo/forgetful-add": programs.addMilk, "todo/forgetful-list": programs.list,
  "todo/model-once": programs.completeOne, "todo/model-twice": programs.completeOne,
  "todo/toggling-once": programs.completeOne, "todo/toggling-twice": programs.completeOne
}

/** The wait after an act: rc.112 runs a dispatcher's tasks in one macrotask, and a task may arm
 * another, so the run waits a fixed number of turns, as the keyed lane's plain run does. */
const turns = async (): Promise<void> => { for (let turn = 0; turn < 64; turn++) await setImmediate() }

interface Performed { recording: KeyedRecording; exit: Json; measured: Record<string, Json>; predicted: Record<string, Json> }

/** Perform one script on the consumer's program: act out each row of the script, then read what
 * the host holds at the script's end. */
const perform = async (fixture: ScenarioFixture, program: Effect.Effect<unknown, unknown, unknown>): Promise<Performed> => {
  const view: KeyedFixture = { name: fixture.name, expression: "", table: fixture.table, source: null,
    plan: fixture.calls.map((call, callId) => ({ ...call, callId })), expected: null, scripted: true }
  const recorder = new KeyedRecorder(view, fixture.session), host = new ScriptedHost(recorder)
  const clock = await Rc112ClockBoundary.make()
  declareScenario(fixture.name, fixture.table)
  const main = provideScenario(fixture.name, fixture.services ?? [], Service, program)
  let root: Fiber.Fiber<unknown, unknown> | undefined, exit: Exit.Exit<unknown, unknown> | undefined
  bindScenario(fixture.name, host)
  try {
    for (const act of fixture.acts) {
      clock.check()
      switch (act.kind) {
        case "evaluate": {
          if (root || act.fiber !== 0) throw Error(`${fixture.name}: only the root starts, and once`)
          root = Effect.runFork(clock.provide(main))
          recorder.attachRoot(root)
          root.addObserver(result => { exit = result })
          break
        }
        case "flush": recorder.flush(); await turns(); break
        case "advanceClock": await recorder.advanceClock(clock, act.millis); await turns(); break
        case "cancel": recorder.cancel(act.fiber); await turns(); break
        case "call": recorder.hold(act); break
        case "reply": host.stage(act.completion); await recorder.arrive(act); break
        case "apply": recorder.apply(act); await turns(); break
      }
    }
    clock.check()
    if (!root) throw Error(`${fixture.name}: the script never starts the root`)
    const end: HostEnd = { exit: exit === undefined ? null : recorder.exitOf(exit), ledger: recorder.measurements() }
    const { measured, predicted } = measure(fixture, end, {})
    return { recording: recorder.snapshot(), exit: end.exit, measured, predicted }
  } finally {
    bindScenario(fixture.name, undefined)
    root?.interruptUnsafe()
    await clock.dispose()
  }
}

/** The host's part of a run's comparison: each entry that the host measured, and each refusal
 * that the ledger predicted, is the entry of Lean's observation of the script. */
const compare = (fixture: ScenarioFixture, run: Pick<Performed, "measured" | "predicted">): void => {
  for (const [field, value] of Object.entries({ ...run.measured, ...run.predicted }))
    deepStrictEqual(value, fixture.observation[field], `${fixture.name}: the host's ${field} is not the Lean machine's`)
}

const manifest = JSON.parse(await readFile(scenariosPath, "utf8")) as ScenarioManifest
const fixtures = manifest.runs.filter(run => run.scenario === "todo")
const unknown = fixtures.filter(fixture => programOf[fixture.name] === undefined).map(fixture => fixture.name)
if (unknown.length) throw Error(`no consumer program for the scripts ${unknown.join(", ")}`)
await mkdir(outPath, { recursive: true })
const cases: Array<{ name: string; recording: KeyedRecording }> = []
const hosts: Array<{ name: string; exit: Json; measured: Record<string, Json>; predicted: Record<string, Json> }> = []
for (const fixture of fixtures) {
  const run = await perform(fixture, programOf[fixture.name]!)
  compare(fixture, run)
  cases.push({ name: fixture.name, recording: run.recording })
  hosts.push({ name: fixture.name, exit: run.exit, measured: run.measured, predicted: run.predicted })
}
// Red control of the comparison: one changed expectation fails by the run's name, at the entry.
const first = fixtures[0]!, firstRun = hosts[0]!
throws(() => compare({ ...first, observation: { ...first.observation, outcome: { changed: true } } }, firstRun),
  (error: unknown) => error instanceof AssertionError && error.message.startsWith(`${first.name}: the host's outcome`))
// Red control of the consumer's program: a script run on another method's program makes a call
// that the script's plan does not hold, and the recorder refuses it.
const milk = fixtures.find(fixture => fixture.name === "todo/milk")!
let refused = false
try { await perform(milk, programs.list) } catch (error) { refused = error instanceof Error && error.message.startsWith("call association differs") }
if (!refused) throw Error("todo/milk run on `list` must be refused by the recorder")
await writeFile(resolve(outPath, "service-cases.json"), JSON.stringify(cases) + "\n")
await writeFile(resolve(outPath, "service-host.json"), JSON.stringify(hosts, null, 2) + "\n")
console.log(`PASS the to-do's service on rc.112: ${fixtures.length} scripts performed on its consumer's programs, ` +
  `each with the host's outcome, calls and predicted refusals equal to Lean's observation; ` +
  `${manifest.waiting.filter(run => run.scenario === "todo").length} scripts with no host run; 2 red controls`)
