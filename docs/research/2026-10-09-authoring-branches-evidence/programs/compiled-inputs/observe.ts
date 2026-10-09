import { Effect } from "effect"
import { pathToFileURL } from "node:url"
import { readFileSync } from "node:fs"

const folder = process.argv[2]
if (!folder) throw new Error("Missing emitted packet directory")
const manifest = JSON.parse(readFileSync(`${folder}/manifest.json`, "utf8"))
const rows = []
for (const c of manifest.cases) {
  const loaded = await import(pathToFileURL(`${folder}/${c.file}`).href)
  const observed = Effect.runSync(loaded.main)
  if (typeof observed !== "number" || !Number.isSafeInteger(observed) || observed < 0) {
    throw new Error(`${c.id}: expected a natural-number observation`)
  }
  rows.push({ id: c.id, observed })
}
console.log(JSON.stringify(rows))
