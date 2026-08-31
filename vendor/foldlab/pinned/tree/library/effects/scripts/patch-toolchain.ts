/**
 * The dev-install toolchain patch, made safe for every context that
 * runs `prepare`.
 *
 * `effect-tsgo patch --typescript --oxlint` grafts the Effect language
 * service into the locally installed typescript (tsgo) and the
 * type-aware rules into oxlint — a MUTATION OF node_modules, wanted
 * exactly once per dev install. But `prepare` also runs under
 * `bun pm pack` / `npm pack`, where the `.bin` shims are not on PATH
 * (probed: the bare `effect-tsgo` invocation dies there and kills the
 * pack). So this wrapper:
 *
 *   - resolves the patcher by PATH-independent module path and runs it
 *     when present — the dev-install case;
 *   - skips with a notice (exit 0) when it is not — the pack/publish
 *     case, where consumers install only `dependencies` and no
 *     patching is wanted or possible.
 *
 * The patch remains a dev-tree concern only: nothing in `dist` or the
 * published tarball depends on it having run (the build compiles with
 * the same tsc either way; the patch adds diagnostics, not emit).
 */
import { existsSync } from "node:fs"
import { join } from "node:path"
import { fileURLToPath } from "node:url"

const packageRoot = fileURLToPath(new URL("..", import.meta.url))
const patcher = join(
  packageRoot,
  "node_modules",
  "@effect",
  "tsgo",
  "dist",
  "effect-tsgo.cjs",
)

if (!existsSync(patcher)) {
  console.log(
    "toolchain patch: @effect/tsgo not installed (pack or dependency install) — skipped",
  )
  process.exit(0)
}

const run = Bun.spawnSync(
  [process.execPath, patcher, "patch", "--typescript", "--oxlint"],
  { cwd: packageRoot, stdout: "inherit", stderr: "inherit" },
)
process.exit(run.exitCode ?? 1)
