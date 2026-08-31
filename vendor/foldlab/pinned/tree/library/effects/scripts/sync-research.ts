/**
 * Research-pack snapshot sync (M1 deliverable).
 *
 * Check mode (default): assert every research/docs copy is byte-equal to
 * its canonical owner under the repository docs/ tree; exit 1 listing stale
 * copies otherwise. Write mode (--write): refresh the copies from the
 * canonical owners. The copies never become authorities; no claim may cite
 * a copied path when a canonical path exists.
 */
import { existsSync, readFileSync, writeFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const pkg = join(dirname(fileURLToPath(import.meta.url)), "..")
const repo = join(pkg, "..", "..")

const copies: ReadonlyArray<readonly [copy: string, canonical: string]> = [
  [
    "research/docs/research/effect-operational-semantics-reference-sweep.md",
    "docs/research/effect-operational-semantics-reference-sweep.md",
  ],
  [
    "research/docs/research/effect-runtime-ground-truth-extraction-scope.md",
    "docs/research/effect-runtime-ground-truth-extraction-scope.md",
  ],
  [
    "research/docs/research/effect-modeling-wasm-interoperability-optimization-frontier.md",
    "docs/research/effect-modeling-wasm-interoperability-optimization-frontier.md",
  ],
  [
    "research/docs/effect-typescript-semantics/README.md",
    "docs/effect-typescript-semantics/README.md",
  ],
  [
    "research/docs/effect-typescript-semantics/CONTEXT.md",
    "docs/effect-typescript-semantics/CONTEXT.md",
  ],
  [
    "research/docs/effect-typescript-semantics/CLAIM-GATES.md",
    "docs/effect-typescript-semantics/CLAIM-GATES.md",
  ],
  [
    "research/docs/effect-typescript-semantics/IMPLEMENTATION-PLAN.md",
    "docs/effect-typescript-semantics/IMPLEMENTATION-PLAN.md",
  ],
]

const write = process.argv.includes("--write")
let stale = 0
for (const [copy, canonical] of copies) {
  const src = readFileSync(join(repo, canonical))
  const dstPath = join(pkg, copy)
  const dst = existsSync(dstPath) ? readFileSync(dstPath) : Buffer.alloc(0)
  if (!src.equals(dst)) {
    if (write) {
      writeFileSync(dstPath, src)
      console.log(`refreshed ${copy}`)
    } else {
      console.error(`stale ${copy}`)
      stale++
    }
  }
}
if (stale > 0) {
  console.error(`${stale} stale copies; run: mise run gen:effects:research`)
  process.exit(1)
}
console.log(
  write
    ? "research copies refreshed from canonical owners"
    : "research copies byte-equal to canonical owners",
)
