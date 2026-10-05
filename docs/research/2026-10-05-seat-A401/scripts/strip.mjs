// Seat A401 (2026-10-05). Strip the comments of every source file of one tree, by the parser's
// own comment spans, and record a digest of each file's syntax tree without positions.
//
// Run: bun strip.mjs <oxc-parser entry> <input root> <output root> <facts.json> [ext ...]
//
// For each file under <input root> whose name ends in one of the extensions (default: .ts):
//   * <output root>/<rel>      the same text with every comment character replaced by a space.
//                              Line breaks are kept, so line N of the output is line N of the input.
//   * facts[<rel>]             { bytes, sha256, lines, comments, errors, ast }
//                              `ast` is the SHA-256 of the syntax tree serialised without the
//                              `start` and `end` fields: equal digests mean equal syntax, whatever
//                              the comments and the layout.
// The parser is oxc-parser, the one the ingest uses (ts/eff/ingest/oxc.ts). Nothing is executed
// from the input tree.
import { createHash } from "node:crypto"
import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from "node:fs"
import { dirname, join, relative } from "node:path"

const [oxcEntry, inRoot, outRoot, factsPath, ...extArgs] = process.argv.slice(2)
if (!oxcEntry || !inRoot || !outRoot || !factsPath) {
  console.error("usage: bun strip.mjs <oxc-parser entry> <input root> <output root> <facts.json> [ext ...]")
  process.exit(2)
}
const exts = extArgs.length > 0 ? extArgs : [".ts"]
const { parseSync } = await import(oxcEntry)

const walk = (dir) => {
  const out = []
  for (const name of readdirSync(dir).sort()) {
    const p = join(dir, name)
    const st = statSync(p)
    if (st.isDirectory()) out.push(...walk(p))
    else if (exts.some((e) => name.endsWith(e)) && !name.endsWith(".d.ts")) out.push(p)
  }
  return out
}

const sha = (text) => createHash("sha256").update(text).digest("hex")
// A BigInt literal's value is not JSON; its `raw` text stays in the tree, and the value is tagged.
const dropPositions = (key, value) =>
  key === "start" || key === "end" ? undefined : typeof value === "bigint" ? `bigint:${value}` : value

const facts = {}
let failed = 0
for (const file of walk(inRoot)) {
  const rel = relative(inRoot, file)
  const bytes = readFileSync(file)
  const source = bytes.toString("utf8")
  const lang = file.endsWith(".ts") ? "ts" : "js"
  const result = parseSync(rel, source, { lang, sourceType: "module" })
  const chars = Array.from({ length: source.length }, (_, i) => source[i])
  let badSpan = 0
  for (const c of result.comments) {
    const head = source.slice(c.start, c.start + 2)
    if (head !== "//" && head !== "/*") badSpan++
    for (let i = c.start; i < c.end; i++) if (chars[i] !== "\n" && chars[i] !== "\r") chars[i] = " "
  }
  const stripped = chars.join("")
  const out = join(outRoot, rel)
  mkdirSync(dirname(out), { recursive: true })
  writeFileSync(out, stripped)
  const errors = result.errors.length
  if (errors > 0 || badSpan > 0) failed++
  facts[rel] = {
    bytes: bytes.length,
    sha256: sha(bytes),
    lines: source.split("\n").length - (source.endsWith("\n") ? 1 : 0),
    comments: result.comments.length,
    badSpan,
    errors,
    ast: sha(JSON.stringify(result.program, dropPositions))
  }
}
writeFileSync(factsPath, JSON.stringify(facts, null, 1))
console.log(`${Object.keys(facts).length} files stripped from ${inRoot}; ${failed} with parse errors or a bad comment span`)
