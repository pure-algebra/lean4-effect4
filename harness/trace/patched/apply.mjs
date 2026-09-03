#!/usr/bin/env node
// Build the patched rc.112 copy (plan packet P-T11, ruling R3 phase 2).
//
//   node harness/trace/patched/apply.mjs [--print]
//   env EFFECT4_EFFECT_NODE_MODULES   the exact pinned installation to copy from
//
// Copies the `effect` package into harness/trace/patched/_copy/node_modules/,
// symlinks every other entry of the pinned node_modules beside it (so the pin
// checks and `effect-tsgo` resolve unchanged), applies the hunks of
// patch-manifest.json (each `find` must occur exactly once), and writes
// trace-host-pin.json: the base pin plus the manifest digest and the digest of
// every patched file before and after. The copy is never committed; it is
// only ever selected through EFFECT4_EFFECT_NODE_MODULES.
import { cpSync, existsSync, lstatSync, mkdirSync, readdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from "node:fs"
import { createHash } from "node:crypto"
import { dirname, join, resolve } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const source = resolve(process.env.EFFECT4_EFFECT_NODE_MODULES ??
  join(process.env.HOME, "Dev/foldlab/library/effects/node_modules"))
const copyRoot = join(here, "_copy")
const target = join(copyRoot, "node_modules")
const manifestPath = join(here, "patch-manifest.json")
const manifest = JSON.parse(readFileSync(manifestPath, "utf8"))
const sha = (data) => createHash("sha256").update(data).digest("hex")

if (process.argv.includes("--print")) { console.log(target); process.exit(0) }

rmSync(copyRoot, { recursive: true, force: true })
mkdirSync(target, { recursive: true })
for (const entry of readdirSync(source)) {
  const from = join(source, entry), to = join(target, entry)
  if (entry === manifest.package) cpSync(from, to, { recursive: true, dereference: true })
  else symlinkSync(from, to, lstatSync(from).isDirectory() ? "dir" : "file")
}
const version = JSON.parse(readFileSync(join(target, manifest.package, "package.json"), "utf8")).version
if (version !== manifest.version) throw new Error(`pin mismatch: manifest patches ${manifest.version}, installation is ${version}`)

const applied = []
for (const hunk of manifest.hunks) {
  const path = join(target, manifest.package, hunk.file)
  const before = readFileSync(path, "utf8")
  const first = before.indexOf(hunk.find)
  if (first < 0) throw new Error(`hunk ${hunk.id}: anchor not found in ${hunk.file}`)
  if (before.indexOf(hunk.find, first + 1) >= 0) throw new Error(`hunk ${hunk.id}: anchor occurs more than once in ${hunk.file}`)
  const after = before.slice(0, first) + hunk.replace + before.slice(first + hunk.find.length)
  writeFileSync(path, after)
  applied.push({ id: hunk.id, census: hunk.census, file: hunk.file, before: sha(before), after: sha(after) })
}
const basePin = existsSync(join(here, "..", "host-pin.json")) ? JSON.parse(readFileSync(join(here, "..", "host-pin.json"), "utf8")) : {}
writeFileSync(join(here, "trace-host-pin.json"), JSON.stringify({
  ...basePin,
  patched: { manifest: "harness/trace/patched/patch-manifest.json", manifestSha256: sha(readFileSync(manifestPath)), hunks: applied }
}, null, 2) + "\n")
console.log(`PASS patched copy at ${target}: ${applied.length} hunks applied to effect@${version}`)
