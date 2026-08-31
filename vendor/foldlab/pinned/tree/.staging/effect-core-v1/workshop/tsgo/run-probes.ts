import { readFileSync } from "node:fs"
import { dirname, join, relative, resolve, sep } from "node:path"
import { fileURLToPath } from "node:url"

const HERE = dirname(fileURLToPath(import.meta.url))
const ROOT = resolve(HERE, "../../../..")
const EFFECTS_ROOT = join(ROOT, "library/effects")
const CLI = join(EFFECTS_ROOT, "node_modules/.bin/effect-tsgo")
const TSC = join(EFFECTS_ROOT, "node_modules/.bin/tsc")
const WORKSHOP_PACKAGE = join(HERE, "package.json")
const BASE_CONFIG = join(HERE, "tsconfig.base.json")
const INSTALLED_EFFECT_PACKAGE = join(EFFECTS_ROOT, "node_modules/effect/package.json")
const INSTALLED_TSGO_PACKAGE = join(EFFECTS_ROOT, "node_modules/@effect/tsgo/package.json")
const INSTALLED_TYPESCRIPT_PACKAGE = join(EFFECTS_ROOT, "node_modules/typescript/package.json")
const EXPECTED_EFFECT_PATHS = {
  effect: ["../../../../library/effects/node_modules/effect/dist/index.d.ts"],
  "effect/*": ["../../../../library/effects/node_modules/effect/dist/*.d.ts"]
} as const

type Project = {
  name: string
  directory: string
  source: string
  expectedDiagnostic?: string
}

const PROJECTS: ReadonlyArray<Project> = [
  { name: "positive", directory: "positive", source: "generated.ts" },
  {
    name: "floating-effect",
    directory: "floating-effect",
    source: "mutant.ts",
    expectedDiagnostic: "floatingEffect"
  },
  {
    name: "missing-effect-error",
    directory: "missing-effect-error",
    source: "mutant.ts",
    expectedDiagnostic: "missingEffectError"
  },
  {
    name: "lazy-promise-in-sync",
    directory: "lazy-promise-in-sync",
    source: "mutant.ts",
    expectedDiagnostic: "lazyPromiseInEffectSync"
  }
]

type JsonRecord = Record<string, unknown>

type Diagnostic = {
  file: string
  severity: string
  code: number
  name: string
  message: string
}

type FileResult = {
  file: string
  detectedEffect: string
  supportedEffect: string
}

type DiagnosticsOutput = {
  diagnostics: ReadonlyArray<Diagnostic>
  files: ReadonlyArray<FileResult>
  summary: {
    filesChecked: number
    totalFiles: number
    errors: number
    warnings: number
    messages: number
  }
}

const isRecord = (value: unknown): value is JsonRecord =>
  typeof value === "object" && value !== null && !Array.isArray(value)

const packageIdentity = (path: string): { name: string; version: string } => {
  const value: unknown = JSON.parse(readFileSync(path, "utf8"))
  if (!isRecord(value) || typeof value.name !== "string" || typeof value.version !== "string") {
    throw new Error(`invalid package identity at ${path}`)
  }
  return { name: value.name, version: value.version }
}

const packageJson = (path: string): JsonRecord => {
  const value: unknown = JSON.parse(readFileSync(path, "utf8"))
  if (!isRecord(value)) throw new Error(`invalid package JSON at ${path}`)
  return value
}

const dependencyVersion = (manifest: JsonRecord, group: string, name: string): string => {
  const dependencies = manifest[group]
  if (!isRecord(dependencies) || typeof dependencies[name] !== "string") {
    throw new Error(`missing exact ${group}.${name} in workshop package.json`)
  }
  const version = dependencies[name]
  if (/^[~^<>=*]/.test(version) || version.includes(" ") || version.includes("||")) {
    throw new Error(`non-exact version ${group}.${name}=${version}`)
  }
  return version
}

const arraysEqual = (left: unknown, right: ReadonlyArray<string>): boolean =>
  Array.isArray(left) && left.length === right.length &&
  left.every((value, index) => value === right[index])

const readEffectPathConfig = (): {
  exact: boolean
} => {
  const config = packageJson(BASE_CONFIG)
  const compilerOptions = config.compilerOptions
  if (!isRecord(compilerOptions)) throw new Error("tsconfig.base.json has no compilerOptions")
  const paths = compilerOptions.paths
  if (!isRecord(paths)) throw new Error("tsconfig.base.json has no paths mapping")
  return {
    exact: compilerOptions.baseUrl === undefined &&
      arraysEqual(paths.effect, EXPECTED_EFFECT_PATHS.effect) &&
      arraysEqual(paths["effect/*"], EXPECTED_EFFECT_PATHS["effect/*"]) &&
      resolve(HERE, EXPECTED_EFFECT_PATHS.effect[0]) ===
        join(EFFECTS_ROOT, "node_modules/effect/dist/index.d.ts")
  }
}

const requireString = (record: JsonRecord, key: string): string => {
  const value = record[key]
  if (typeof value !== "string") throw new Error(`diagnostics JSON ${key} is not a string`)
  return value
}

const requireNumber = (record: JsonRecord, key: string): number => {
  const value = record[key]
  if (typeof value !== "number") throw new Error(`diagnostics JSON ${key} is not a number`)
  return value
}

const decodeDiagnostics = (text: string): DiagnosticsOutput => {
  const value: unknown = JSON.parse(text)
  if (!isRecord(value) || !Array.isArray(value.diagnostics) ||
      !Array.isArray(value.files) || !isRecord(value.summary)) {
    throw new Error("unexpected effect-tsgo diagnostics JSON shape")
  }
  const diagnostics = value.diagnostics.map((entry): Diagnostic => {
    if (!isRecord(entry)) throw new Error("malformed diagnostic row")
    return {
      file: requireString(entry, "file"),
      severity: requireString(entry, "severity"),
      code: requireNumber(entry, "code"),
      name: requireString(entry, "name"),
      message: requireString(entry, "message")
    }
  })
  const files = value.files.map((entry): FileResult => {
    if (!isRecord(entry)) throw new Error("malformed checked-file row")
    return {
      file: requireString(entry, "file"),
      detectedEffect: requireString(entry, "detectedEffect"),
      supportedEffect: requireString(entry, "supportedEffect")
    }
  })
  return {
    diagnostics,
    files,
    summary: {
      filesChecked: requireNumber(value.summary, "filesChecked"),
      totalFiles: requireNumber(value.summary, "totalFiles"),
      errors: requireNumber(value.summary, "errors"),
      warnings: requireNumber(value.summary, "warnings"),
      messages: requireNumber(value.summary, "messages")
    }
  }
}

const normalize = (path: string): string => path.split(sep).join("/")

const setEquals = (left: ReadonlyArray<string>, right: ReadonlyArray<string>): boolean => {
  const leftSorted = [...new Set(left)].sort((a, b) => a.localeCompare(b))
  const rightSorted = [...new Set(right)].sort((a, b) => a.localeCompare(b))
  return leftSorted.length === rightSorted.length &&
    leftSorted.every((value, index) => value === rightSorted[index])
}

const results: Array<JsonRecord> = []
const failures: Array<string> = []
const workshopManifest = packageJson(WORKSHOP_PACKAGE)
const expectedEffectVersion = dependencyVersion(workshopManifest, "dependencies", "effect")
const expectedTsgoVersion = dependencyVersion(workshopManifest, "devDependencies", "@effect/tsgo")
const expectedTypescriptVersion = dependencyVersion(workshopManifest, "devDependencies", "typescript")
const installedEffect = packageIdentity(INSTALLED_EFFECT_PACKAGE)
const installedTsgo = packageIdentity(INSTALLED_TSGO_PACKAGE)
const installedTypescript = packageIdentity(INSTALLED_TYPESCRIPT_PACKAGE)
const effectPathConfig = readEffectPathConfig()

if (installedEffect.name !== "effect" || installedEffect.version !== expectedEffectVersion) {
  failures.push(`installed Effect identity/version mismatch: ${installedEffect.name}@${installedEffect.version}`)
}
if (installedTsgo.name !== "@effect/tsgo" || installedTsgo.version !== expectedTsgoVersion) {
  failures.push(`installed Effect tsgo identity/version mismatch: ${installedTsgo.name}@${installedTsgo.version}`)
}
if (installedTypescript.name !== "typescript" || installedTypescript.version !== expectedTypescriptVersion) {
  failures.push(
    `installed TypeScript identity/version mismatch: ${installedTypescript.name}@${installedTypescript.version}`
  )
}
if (!effectPathConfig.exact) {
  failures.push("tsconfig Effect path does not resolve exactly through library/effects/node_modules/effect")
}

const versionResult = Bun.spawnSync([CLI, "--version"], {
  cwd: EFFECTS_ROOT,
  stdout: "pipe",
  stderr: "pipe"
})
const cliVersion = new TextDecoder().decode(versionResult.stdout).trim()
const cliVersionExact = versionResult.exitCode === 0 &&
  new TextDecoder().decode(versionResult.stderr).trim() === "" &&
  cliVersion === `tsgo v${expectedTsgoVersion}`
if (!cliVersionExact) failures.push(`effect-tsgo CLI version mismatch: ${cliVersion}`)

const positiveProject = join(HERE, "positive/tsconfig.json")
const resolutionResult = Bun.spawnSync([
  TSC,
  "--project",
  positiveProject,
  "--traceResolution",
  "--noEmit"
], {
  cwd: ROOT,
  stdout: "pipe",
  stderr: "pipe"
})
const resolutionTrace = normalize(new TextDecoder().decode(resolutionResult.stdout))
const resolutionStderr = new TextDecoder().decode(resolutionResult.stderr).trim()
const expectedEffectEntry = normalize(join(EFFECTS_ROOT, "node_modules/effect/dist/index.d.ts"))
const forbiddenBridgeRoot = normalize(join(HERE, "node_modules/effect"))
const exactResolutionLine =
  `Module name 'effect' was successfully resolved to '${expectedEffectEntry}'`
const resolutionVerified = resolutionResult.exitCode === 0 && resolutionStderr === "" &&
  resolutionTrace.includes(exactResolutionLine) &&
  !resolutionTrace.includes(forbiddenBridgeRoot)
if (!resolutionVerified) {
  failures.push("TypeScript did not resolve effect directly to the installed library/effects package")
}

const compilerVersionResult = Bun.spawnSync([TSC, "--version"], {
  cwd: EFFECTS_ROOT,
  stdout: "pipe",
  stderr: "pipe"
})
const compilerVersion = new TextDecoder().decode(compilerVersionResult.stdout).trim()
const expectedCompilerVersion =
  `Version ${expectedTypescriptVersion}+effect-tsgo.${expectedTsgoVersion}`
const compilerVersionExact = compilerVersionResult.exitCode === 0 &&
  new TextDecoder().decode(compilerVersionResult.stderr).trim() === "" &&
  compilerVersion === expectedCompilerVersion
if (!compilerVersionExact) failures.push(`patched TypeScript compiler version mismatch: ${compilerVersion}`)

for (const project of PROJECTS) {
  const projectPath = join(HERE, project.directory, "tsconfig.json")
  const expectedFile = normalize(join(HERE, project.directory, project.source))
  const args = [
    "diagnostics",
    "--project",
    projectPath,
    "--format",
    "json",
    "--list-files",
    "--strict"
  ]
  const processResult = Bun.spawnSync([CLI, ...args], {
    cwd: EFFECTS_ROOT,
    stdout: "pipe",
    stderr: "pipe"
  })
  const stdout = new TextDecoder().decode(processResult.stdout)
  const stderr = new TextDecoder().decode(processResult.stderr)
  const decoded = decodeDiagnostics(stdout)
  const diagnosticNames = decoded.diagnostics
    .map((diagnostic) => diagnostic.name)
    .sort((left, right) => left.localeCompare(right))
  const checkedFiles = decoded.files.map((file) => normalize(file.file))
  const fileSetEqual = setEquals(checkedFiles, [expectedFile])
  const exactCounts = decoded.summary.filesChecked === 1 && decoded.summary.totalFiles === 1
  const versionsAreV4 = decoded.files.every((file) =>
    file.detectedEffect === "v4" && file.supportedEffect === "v4")
  const expectedExit = project.expectedDiagnostic === undefined ? 0 : 1
  const exactDiagnostic = project.expectedDiagnostic === undefined
    ? diagnosticNames.length === 0
    : diagnosticNames.length === 1 && diagnosticNames[0] === project.expectedDiagnostic
  const exitIsStrict = processResult.exitCode === expectedExit

  if (!fileSetEqual) failures.push(`${project.name}: generated-file set mismatch`)
  if (!exactCounts) failures.push(`${project.name}: filesChecked/totalFiles is not 1/1`)
  if (!versionsAreV4) failures.push(`${project.name}: Effect v4 not detected/supported`)
  if (!exactDiagnostic) failures.push(`${project.name}: unexpected diagnostics ${diagnosticNames.join(",")}`)
  if (!exitIsStrict) failures.push(`${project.name}: expected strict exit ${expectedExit}, got ${processResult.exitCode}`)
  if (stderr.trim().length > 0) failures.push(`${project.name}: unexpected stderr`)

  results.push({
    project: project.name,
    command: ["./node_modules/.bin/effect-tsgo", ...args.map((arg) =>
      normalize(arg).replace(normalize(ROOT), "<repo>"))],
    expectedFile: normalize(relative(ROOT, expectedFile)),
    checkedFiles: checkedFiles.map((file) => normalize(relative(ROOT, file))).sort(),
    fileSetEqual,
    summary: decoded.summary,
    diagnostics: decoded.diagnostics.map((diagnostic) => ({
      name: diagnostic.name,
      severity: diagnostic.severity,
      code: diagnostic.code,
      file: normalize(relative(ROOT, diagnostic.file)),
      message: diagnostic.message
    })),
    expectedDiagnostic: project.expectedDiagnostic ?? null,
    expectedExit,
    actualExit: processResult.exitCode,
    strictExitVerified: exitIsStrict,
    detectedEffectV4: versionsAreV4,
    stderr
  })
}

const output = {
  schemaVersion: "foldlab.effect-tsgo-probes.v1",
  status: failures.length === 0 ? "ok" : "error",
  cwd: "library/effects",
  cli: "node_modules/.bin/effect-tsgo",
  packageResolution: {
    workshopManifest: ".staging/effect-core-v1/workshop/tsgo/package.json",
    baseConfig: ".staging/effect-core-v1/workshop/tsgo/tsconfig.base.json",
    baseUrl: null,
    paths: EXPECTED_EFFECT_PATHS,
    exactInstalledPath: effectPathConfig.exact,
    installedPackage: "library/effects/node_modules/effect/package.json",
    expectedEffectVersion,
    installedEffectVersion: installedEffect.version,
    exactEffectVersion: installedEffect.version === expectedEffectVersion,
    expectedTsgoVersion,
    installedTsgoVersion: installedTsgo.version,
    cliVersion,
    cliVersionExact,
    expectedTypescriptVersion,
    installedTypescriptVersion: installedTypescript.version,
    compilerVersion,
    compilerVersionExact,
    resolutionVerified,
    resolvedEffectEntry: resolutionVerified ? expectedEffectEntry.replace(normalize(ROOT), "<repo>") : null,
    forbiddenBridgeObserved: resolutionTrace.includes(forbiddenBridgeRoot),
    declarationTarget: "library/effects/node_modules/effect/dist/index.d.ts"
  },
  projects: results,
  failures
}

process.stdout.write(`${JSON.stringify(output, null, 2)}\n`)
if (failures.length > 0) process.exitCode = 1
