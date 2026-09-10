/** Thin runner: consume Lean-produced fixture text/table metadata, execute that exact
 * generated expression with the selected binding, and save new-version evidence. */
import { mkdir, readFile, writeFile } from "node:fs/promises"
import { dirname, relative, resolve } from "node:path"
import { pathToFileURL } from "node:url"
import { ScalarRecorder } from "./record.ts"
import type { Json } from "./protocol.ts"

interface Fixture { profile: string; name: string; expression: string; table: Json[]; natBound: number }
const [manifestPath, outputPath] = process.argv.slice(2)
if (!manifestPath || !outputPath) throw new Error("usage: bun run run.ts LEAN_MANIFEST OUTPUT_DIRECTORY")
const manifest = JSON.parse(await readFile(manifestPath, "utf8")) as { fixtures: Fixture[] }
const output = resolve(outputPath)
await mkdir(output, { recursive: true })
const records = []
for (const fixture of manifest.fixtures.filter(f => f.profile === "serial-root-scalar-v1")) {
  if (!["two", "failure"].includes(fixture.name)) throw new Error("unexpected fixture")
  const recorder = new ScalarRecorder(`effect4-${fixture.name}-session-1`, { program: fixture.name,
    table: fixture.table, natBound: fixture.natBound }, fixture.name === "failure" ? 7 : undefined)
  const modulePath = resolve(output, `${fixture.name}.ts`)
  const recorderImport = "./" + relative(dirname(modulePath), resolve(import.meta.dir, "record.ts"))
  // The output remains beneath this harness so package resolution uses its pinned Effect.
  await writeFile(modulePath, `import { Effect } from "effect"\nimport type { ScalarRecorder } from ${JSON.stringify(recorderImport)}\nexport const build = (Host: ScalarRecorder["Host"]) => ${fixture.expression}\n`)
  const generated = await import(pathToFileURL(modulePath).href)
  const result = await recorder.run(generated.build(recorder.Host))
  const recordingPath = resolve(output, `${fixture.name}.json`)
  await writeFile(recordingPath, JSON.stringify(result.recording, null, 2) + "\n")
  records.push({ name: fixture.name, records: result.recording.records.length, recording: recordingPath,
    leanExpression: fixture.expression, hostCompletion: result.completion })
}
await writeFile(resolve(output, "receipt.json"), JSON.stringify({ kind: "actual-effect-serial-scalar-recording", records }, null, 2) + "\n")
console.log(JSON.stringify({ kind: "actual-effect-serial-scalar-recording", records }))
