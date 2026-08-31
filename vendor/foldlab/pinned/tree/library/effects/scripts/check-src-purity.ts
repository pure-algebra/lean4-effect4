/**
 * The Effect-boundary purity gate: nothing under src/ may run an
 * Effect itself. Runtime execution belongs to callers (and tests);
 * a run or unsafe call inside the library escapes structured error
 * handling, interruption, and layer scoping silently.
 */
import { readdirSync, readFileSync, statSync } from "node:fs"
import { join, relative } from "node:path"
import { fileURLToPath } from "node:url"

const forbidden =
  /\bEffect\.(runSync|runSyncExit|runPromise|runPromiseExit|runFork|runCallback)\b|\brunMain\b|\bunsafeRun\w*\b/

/** NO node:fs, ever (operator ruling 2026-08-28): filesystem is an
 * effect and enters through the FileSystem service. The one sync
 * suite-structure seam is allowlisted. */
const forbiddenFs = /from\s+"node:fs(\/promises)?"/
const fsAllowlist = ["test/conformance/suiteIndex.ts"]
const packageRoot = fileURLToPath(new URL("..", import.meta.url))

const packageRelative = (file: string): string =>
  relative(packageRoot, file).replaceAll("\\", "/")

const walk = (dir: string): Array<string> =>
  readdirSync(dir).flatMap((name) => {
    const path = join(dir, name)
    return statSync(path).isDirectory() ? walk(path)
      : path.endsWith(".ts") ? [path]
      : []
  })

const hits: Array<string> = []
for (const file of walk(join(packageRoot, "src"))) {
  const lines = readFileSync(file, "utf8").split(/\r?\n/)
  lines.forEach((line, index) => {
    if (forbidden.test(line)) {
      hits.push(`${packageRelative(file)}:${index + 1}: ${line.trim()}`)
    }
    if (forbiddenFs.test(line)) {
      hits.push(`${packageRelative(file)}:${index + 1}: node:fs is banned — ${line.trim()}`)
    }
  })
}
for (const file of walk(join(packageRoot, "test"))) {
  if (fsAllowlist.includes(packageRelative(file))) continue
  const lines = readFileSync(file, "utf8").split(/\r?\n/)
  lines.forEach((line, index) => {
    if (forbiddenFs.test(line)) {
      hits.push(`${packageRelative(file)}:${index + 1}: node:fs is banned — ${line.trim()}`)
    }
  })
}

if (hits.length > 0) {
  console.error("src purity gate: runtime execution inside the library:")
  for (const hit of hits) console.error(`  ${hit}`)
  process.exit(1)
}
console.log("src purity gate: no runtime execution under src/")
