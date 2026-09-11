/** Run the exact Lean-printed expressions, then save fresh v2 tapes and host receipts.
 * Binding plans are explicit before execution; none of their completions executes on host. */
import { mkdir, readFile, writeFile } from "node:fs/promises"
import { dirname, relative, resolve } from "node:path"
import { pathToFileURL } from "node:url"
import { setImmediate } from "node:timers/promises"
import { deepStrictEqual } from "node:assert"
import { Effect, type Exit } from "effect"
import { KeyedRecorder, exitJson, type KeyedFixture } from "./keyed-recorder.ts"
import { KeyedBindings } from "./keyed-bindings.ts"
const [manifestPath, outputPath] = process.argv.slice(2)
if (!manifestPath || !outputPath) throw Error("usage: run-keyed.ts LEAN_FIXTURES OUTPUT_DIRECTORY")
const fixtures = JSON.parse(await readFile(manifestPath, "utf8")) as KeyedFixture[]
const output = resolve(outputPath)
await mkdir(output, { recursive: true })
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
    const fiber = Effect.runFork(build(binding))
    fiber.addObserver(exit => { completed = exit })
    try {
      const started = Date.now()
      while (!completed) {
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
      const observed = exitJson(completed)
      deepStrictEqual(observed, order === "apply-BA" ? { success: 1 } : fixture.expected, `${name}: actual rc.112 exit versus finite Lean model`)
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
    }
  }
}
await writeFile(resolve(output, "cases.json"), JSON.stringify(cases) + "\n")
await writeFile(resolve(output, "host.json"), JSON.stringify(receipts, null, 2) + "\n")
console.log(`PASS keyed host: ${receipts.length} actual rc.112 runs; ${fixtures.length} admitted printed programs`)
