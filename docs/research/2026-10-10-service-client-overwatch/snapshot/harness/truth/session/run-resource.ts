/** Run exactly the resource expressions/table metadata emitted by Session.lean. */
import { mkdir, readFile, writeFile } from "node:fs/promises"
import { dirname, relative, resolve } from "node:path"
import { pathToFileURL } from "node:url"
import { Cause, Exit } from "effect"
import { ResourceBinding } from "./resource.ts"
import { decodeResource } from "./resource-protocol.ts"
import type { Json } from "./protocol.ts"

interface Fixture { name: string; profile: string; expression: string; table: Json[]; natBound: number }
const [manifestPath, outputPath] = process.argv.slice(2)
if (!manifestPath || !outputPath) throw Error("usage: bun run run-resource.ts LEAN_MANIFEST OUTPUT_DIRECTORY")
const manifest = JSON.parse(await readFile(manifestPath, "utf8")) as { fixtures: Fixture[] }
const output = resolve(outputPath)
await mkdir(output, { recursive: true })
const receipts = []
for (const fixture of manifest.fixtures.filter(f => f.profile === "serial-root-resource-v1")) {
  const binding = new ResourceBinding(`effect4-${fixture.name}-${crypto.randomUUID()}`)
  const modulePath = resolve(output, `${fixture.name}.ts`)
  const bindingImport = "./" + relative(dirname(modulePath), resolve(import.meta.dir, "resource.ts"))
  await writeFile(modulePath, `import { Effect } from "effect"\nimport type { ResourceBinding } from ${JSON.stringify(bindingImport)}\nexport const build = (Host: ResourceBinding["Host"]) => ${fixture.expression}\n`)
  const generated = await import(pathToFileURL(modulePath).href)
  const actual = await binding.run(generated.build(binding.Host))
  const recording = decodeResource({ header: { format: "effect4-host-session-v1", version: 1,
    session: binding.session, profile: "serial-root-resource-v1", program: fixture.name,
    table: fixture.table, rootRuntimeFiber: actual.rootRuntimeFiber }, records: actual.records },
    { program: fixture.name, table: fixture.table, natBound: fixture.natBound })
  const observed = Exit.isSuccess(actual.exit) ? { success: actual.exit.value ?? null } : {
    failure: actual.exit.cause.reasons.map(r => Cause.isFailReason(r) ? { fail: r.error } :
      Cause.isDieReason(r) ? { die: { error: r.defect } } : { unsupported: true }) }
  const recordingPath = resolve(output, `${fixture.name}.json`)
  await writeFile(recordingPath, JSON.stringify(recording, null, 2) + "\n")
  receipts.push({ name: fixture.name, expression: fixture.expression, recording: recordingPath,
    hostExit: observed, hostState: actual.state, records: actual.records.length })
}
await writeFile(resolve(output, "resource-receipt.json"), JSON.stringify(receipts, null, 2) + "\n")
console.log(JSON.stringify(receipts))
