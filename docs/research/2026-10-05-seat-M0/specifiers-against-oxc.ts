// Seat M0, 2026-10-05: the static import and re-export specifiers of the given sources, by
// oxc-parser (0.147.0 in the pin's install), as JSON. The seat compared them with the lane's
// own scanner (`specifiers` of scripts/check-truth-release.py) on every source of the work
// copy. Run it from a folder whose node_modules is the pin's install, with `bun --no-install`.
import { parseSync } from "oxc-parser"
import * as fs from "node:fs"
const out: Record<string, string[]> = {}
for (const file of process.argv.slice(2)) {
  const text = fs.readFileSync(file, "utf8")
  const parsed = parseSync(file, text)
  if (parsed.errors.length > 0) throw new Error(`${file}: ${parsed.errors.length} parse errors`)
  const specs: string[] = []
  for (const node of parsed.program.body as any[]) {
    if ((node.type === "ImportDeclaration" || node.type === "ExportAllDeclaration" || node.type === "ExportNamedDeclaration") && node.source)
      specs.push(node.source.value)
  }
  out[file] = specs
}
console.log(JSON.stringify(out))
