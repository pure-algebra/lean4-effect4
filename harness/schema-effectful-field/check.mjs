import { execFileSync, spawnSync } from "node:child_process"
import { cpSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from "node:fs"
import { join, resolve } from "node:path"
import { tmpdir } from "node:os"
import { fileURLToPath } from "node:url"

const here = resolve(fileURLToPath(new URL(".", import.meta.url)))
const nodeModules = resolve(
  process.env.EFFECT4_EFFECT_NODE_MODULES ??
    join(here, "../../../foldlab/library/effects/node_modules")
)

const packageVersion = (name) =>
  JSON.parse(readFileSync(join(nodeModules, name, "package.json"), "utf8")).version

const exact = {
  effect: packageVersion("effect"),
  typescript: packageVersion("typescript"),
  tsgo: packageVersion("@effect/tsgo")
}
if (exact.effect !== "4.0.0-rc.112" || exact.typescript !== "7.0.2" ||
    exact.tsgo !== "0.38.0") {
  throw new Error(`wrong host profile ${JSON.stringify(exact)}`)
}

const originalCompiler = execFileSync("find", [
  nodeModules,
  "-path", "*/@typescript/typescript-*/lib/tsc.original",
  "-type", "f",
  "-print", "-quit"
], { encoding: "utf8" }).trim()
if (originalCompiler.length === 0) throw new Error("unpatched TypeScript compiler missing")

const temporary = mkdtempSync(join(tmpdir(), "effect4-field-"))
try {
  const api = readFileSync(join(here, "api.ts"), "utf8")
  const projects = [
    ["positive", "positive.tail.ts", []],
    ["floating", "floating.tail.ts", ["floatingEffect"]],
    ["missing-error", "missing-error.tail.ts", ["missingEffectError"]],
    ["missing-context", "missing-context.tail.ts", ["missingEffectContext"]]
  ]

  for (const [name, tail, expectedNames] of projects) {
    const directory = join(temporary, name)
    cpSync(here, directory, { recursive: true })
    symlinkSync(nodeModules, join(directory, "node_modules"), "dir")
    writeFileSync(
      join(directory, "fixture.ts"),
      `${api}\n${readFileSync(join(here, tail), "utf8")}`
    )

    const direct = spawnSync(originalCompiler, ["-p", "tsconfig.json", "--pretty", "false"], {
      cwd: directory,
      encoding: "utf8"
    })
    if (direct.status !== 0 || direct.stdout !== "" || direct.stderr !== "") {
      throw new Error(`${name}: direct TypeScript rejected fixture\n${direct.stdout}${direct.stderr}`)
    }

    const result = spawnSync(join(nodeModules, ".bin/effect-tsgo"), [
      "diagnostics", "--project", "tsconfig.json", "--format", "json",
      "--strict", "--list-files"
    ], { cwd: directory, encoding: "utf8" })
    const report = JSON.parse(result.stdout)
    const names = report.diagnostics.map((entry) => entry.name).sort()
    const expected = [...expectedNames].sort()
    const exactNames = names.length === expected.length &&
      names.every((value, index) => value === expected[index])
    const exactFiles = report.summary.filesChecked === 1 &&
      report.summary.totalFiles === 1 && report.files.length === 1
    const v4 = report.files.every((entry) =>
      entry.detectedEffect === "v4" && entry.supportedEffect === "v4")
    const expectedExit = expected.length === 0 ? 0 : 1
    if (!exactNames || !exactFiles || !v4 || result.status !== expectedExit ||
        result.stderr !== "") {
      throw new Error(`${name}: unexpected effect-tsgo result ${JSON.stringify({
        names, expected, summary: report.summary, status: result.status,
        stderr: result.stderr
      })}`)
    }
  }

  const positive = join(temporary, "positive", "fixture.ts")
  const runtime = spawnSync(process.execPath, ["--experimental-strip-types", positive], {
    cwd: join(temporary, "positive"),
    encoding: "utf8",
    env: { ...process.env, NODE_NO_WARNINGS: "1" }
  })
  if (runtime.status !== 0 || !runtime.stdout.includes(
      "schema effectful field: directional types and read/write order passed")) {
    throw new Error(`runtime failed\n${runtime.stdout}${runtime.stderr}`)
  }

  console.log(`schema effectful field: TypeScript ${exact.typescript} passed`)
  console.log(`schema effectful field: Effect ${exact.effect} runtime passed`)
  console.log(`schema effectful field: effect-tsgo ${exact.tsgo} diagnostics passed`)
} finally {
  rmSync(temporary, { recursive: true, force: true })
}
