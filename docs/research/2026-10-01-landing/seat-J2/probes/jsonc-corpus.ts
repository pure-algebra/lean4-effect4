// Seat J2, step 1: the census's JSONC read (`parseJsonc`, ts/eff/ingest/census/corpus.ts) over every
// file the census reads with it: foldlab's manifest and labels, and every package.json the
// `Generations` walk visits (the same excluded directory names). Each file is also read by
// JSON.parse and by bun's own Bun.JSONC.parse; the three are compared value for value.
import { readFileSync, readdirSync, existsSync } from "node:fs"
import { join, resolve } from "node:path"
import { isDeepStrictEqual } from "node:util"
import { parseJsonc, excluded } from "../../../../../ts/eff/ingest/census/corpus.ts"
const root = "/Users/pooks/Dev/foldlab"
const manifest = join(root, "experiments/parser-census/corpus-manifest.json"), labels = join(root, "experiments/parser-census/project-labels.json")
const files = [manifest, labels]
const projects = (parseJsonc(readFileSync(manifest, "utf8")).projects as { localPath: string }[])
const walk = (dir: string) => {
  if (existsSync(join(dir, "package.json"))) files.push(join(dir, "package.json"))
  for (const e of readdirSync(dir, { withFileTypes: true })) if (e.isDirectory() && !excluded.includes(e.name)) walk(join(dir, e.name))
}
for (const p of projects) walk(resolve(root, p.localPath))
let same = 0, jsonFails = 0, jsoncOnly: string[] = [], disagree: string[] = [], refused: string[] = []
for (const f of files) {
  const text = readFileSync(f, "utf8")
  let mine: unknown, plain: unknown, bun: unknown, plainOk = true
  try { mine = parseJsonc(text) } catch (e) { refused.push(`${f}: ${e}`); continue }
  try { plain = JSON.parse(text) } catch { plainOk = false; jsonFails++ }
  try { bun = (Bun as unknown as { JSONC: { parse(s: string): unknown } }).JSONC.parse(text) } catch (e) { disagree.push(`${f}: Bun.JSONC threw ${e}`); continue }
  if (!isDeepStrictEqual(mine, bun)) { disagree.push(`${f}: differs from Bun.JSONC`); continue }
  if (plainOk && !isDeepStrictEqual(mine, plain)) { disagree.push(`${f}: differs from JSON.parse`); continue }
  if (!plainOk) jsoncOnly.push(f)
  same++
}
console.log(`files ${files.length} (projects ${projects.length}); read alike by parseJsonc, Bun.JSONC and (where it reads them) JSON.parse: ${same}; JSON.parse refuses ${jsonFails}; parseJsonc refuses ${refused.length}; disagreements ${disagree.length}`)
for (const f of jsoncOnly) console.log("needs JSONC:", f.replace(root, "<foldlab>"))
for (const f of refused) console.log("refused:", f.replace(root, "<foldlab>"))
for (const f of disagree) console.log("DISAGREE:", f.replace(root, "<foldlab>"))
process.exitCode = refused.length || disagree.length ? 1 : 0
