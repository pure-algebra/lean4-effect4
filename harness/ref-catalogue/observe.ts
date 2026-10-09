import { Effect, Ref } from "effect"
import { pathToFileURL } from "node:url"
import { readFileSync } from "node:fs"

const folder = process.argv[2]
if (!folder) throw new Error("observe: missing packet directory")
const manifest = JSON.parse(readFileSync(`${folder}/manifest.json`, "utf8"))
const rows = []
for (const c of manifest.cases) {
  const loaded = await import(pathToFileURL(`${folder}/${c.file}`).href)
  const observed = Effect.runSync(loaded.main)
  rows.push({ id: c.id, observed })
}
const loaded = await import(pathToFileURL(`${folder}/wrong-update.ts`).href)
const mutant = Effect.runSync(loaded.main)
// Latest's set declaration returns void; the runtime returns its backing MutableRef.
const rawSet = Effect.runSync(Effect.gen(function*() {
  const cell = yield* Ref.make(5)
  const result: unknown = yield* Ref.set(cell, 7)
  return { backing: result === cell.ref, outer: result === cell, next: yield* Ref.get(cell) }
}))
console.log(JSON.stringify({ rows, mutant, rawSet }))
