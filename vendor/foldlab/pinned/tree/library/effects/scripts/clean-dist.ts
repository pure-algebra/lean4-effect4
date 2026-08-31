/** Remove only this package's derived distribution directory. The explicit
 * path check keeps a malformed URL or future relocation from widening the
 * recursive removal target. */
import { rmSync } from "node:fs"
import { basename, dirname, resolve } from "node:path"
import { fileURLToPath } from "node:url"

const packageRoot = resolve(fileURLToPath(new URL("..", import.meta.url)))
const distDir = resolve(fileURLToPath(new URL("../dist", import.meta.url)))

if (dirname(distDir) !== packageRoot || basename(distDir) !== "dist") {
  throw new Error(`refusing to clean unexpected distribution path: ${distDir}`)
}

rmSync(distDir, { force: true, recursive: true })
