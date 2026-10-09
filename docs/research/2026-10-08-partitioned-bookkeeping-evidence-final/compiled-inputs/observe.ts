import { Effect } from "effect"
import { pathToFileURL } from "node:url"
import { readFileSync } from "node:fs"

const folder = process.argv[2]
if (!folder) throw new Error("Missing emitted packet directory")
const manifest = JSON.parse(readFileSync(`${folder}/manifest.json`, "utf8"))
const rows = []
for (const c of manifest.cases) {
  const loaded = await import(pathToFileURL(`${folder}/${c.file}`).href)
  rows.push({ id: c.id, observed: Effect.runSync(loaded.main) })
}
console.log(JSON.stringify(rows))
