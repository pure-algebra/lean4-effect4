/**
 * Pre-grade Effect surface probe.
 *
 * Reads the installed rc.112 package, resolves its exports map against a
 * recursive shipped-file walk, and uses the already-pinned TypeScript 5.9
 * checker to census stable declaration/export coordinates.  The existing
 * runtime bank is read only as an independent completeness cross-check.
 * Nothing is written to the repository; the canonical result is JSON stdout.
 */

import { createHash } from "node:crypto"
import { readFileSync, readdirSync } from "node:fs"
import { dirname, join, relative, resolve, sep } from "node:path"
import { fileURLToPath } from "node:url"
import ts from "../../../experiments/entity-store-extract/node_modules/typescript/lib/typescript.js"

const HERE = dirname(fileURLToPath(import.meta.url))
const ROOT = resolve(HERE, "../../..")
const EFFECT_ROOT = join(ROOT, "library/effects/node_modules/effect")
const PACKAGE_JSON = join(EFFECT_ROOT, "package.json")
const OLD_BANK = join(ROOT, "experiments/lift-harness/models/bank-r0.json")

const SENTINELS = [
  "effect/unstable/http/MultipartParser/HeadersParser",
  "effect/unstable/http/MultipartParser/Search"
] as const

const SUMMARY_ONLY = process.argv.includes("--summary")

const compareText = (left: string, right: string): number =>
  left < right ? -1 : left > right ? 1 : 0

type JsonRecord = Record<string, unknown>

type PackageInfo = {
  name: string
  version: string
  exports: Record<string, string | null>
}

type PublicEntry = {
  specifier: string
  exportKey: string
  js: string
  declaration: string
  source: string
  hasDeclaration: boolean
  hasSource: boolean
  containsInternalSegment: boolean
  stability: "stable" | "testing" | "unstable"
}

type DeclarationCoordinate = {
  file: string
  syntaxKind: string
  start: number
  end: number
  line: number
  column: number
}

type ExposureCoordinate = {
  key: string
  module: string
  exportPath: string
  space: "type" | "value" | "namespace"
  declarations: ReadonlyArray<DeclarationCoordinate>
}

type CanonicalCoordinate = {
  key: string
  module: string
  exportPath: string
  space: "type" | "value" | "namespace"
  declarations: ReadonlyArray<DeclarationCoordinate>
  exposures: ReadonlyArray<string>
}

const isRecord = (value: unknown): value is JsonRecord =>
  typeof value === "object" && value !== null && !Array.isArray(value)

const normalizeSlash = (value: string): string => value.split(sep).join("/")

const packageRelative = (absolute: string): string =>
  normalizeSlash(relative(EFFECT_ROOT, absolute))

const sha256 = (value: unknown): string =>
  createHash("sha256").update(JSON.stringify(value)).digest("hex")

const parsePackage = (text: string): PackageInfo => {
  const value: unknown = JSON.parse(text)
  if (!isRecord(value)) throw new Error("effect package.json is not an object")
  if (typeof value.name !== "string" || typeof value.version !== "string") {
    throw new Error("effect package.json is missing name/version")
  }
  if (!isRecord(value.exports)) throw new Error("effect package.json exports is not an object")

  const exports: Record<string, string | null> = {}
  for (const [key, target] of Object.entries(value.exports)) {
    if (typeof target !== "string" && target !== null) {
      throw new Error(`unsupported conditional exports entry at ${key}`)
    }
    exports[key] = target
  }
  return { name: value.name, version: value.version, exports }
}

const parseOldBankModules = (text: string): ReadonlyArray<string> => {
  const value: unknown = JSON.parse(text)
  if (!isRecord(value) || !Array.isArray(value.modules)) {
    throw new Error("old runtime bank is missing modules")
  }
  const modules: Array<string> = []
  for (const row of value.modules) {
    if (!isRecord(row) || typeof row.module !== "string") {
      throw new Error("old runtime bank contains a malformed module row")
    }
    modules.push(row.module)
  }
  return modules.sort(compareText)
}

const walkFiles = (root: string): ReadonlyArray<string> => {
  const output: Array<string> = []
  const visit = (directory: string): void => {
    const entries = readdirSync(directory, { withFileTypes: true })
      .sort((left, right) => compareText(left.name, right.name))
    for (const entry of entries) {
      const absolute = join(directory, entry.name)
      if (entry.isDirectory()) visit(absolute)
      else if (entry.isFile()) output.push(absolute)
    }
  }
  visit(root)
  return output.sort(compareText)
}

type PatternMatch = {
  key: string
  target: string | null
  capture: string
  prefixLength: number
  suffixLength: number
  order: number
}

const matchPattern = (
  exportKey: string,
  target: string | null,
  subpath: string,
  order: number
): PatternMatch | undefined => {
  const star = exportKey.indexOf("*")
  if (star < 0) return undefined
  const prefix = exportKey.slice(0, star)
  const suffix = exportKey.slice(star + 1)
  if (!subpath.startsWith(prefix) || !subpath.endsWith(suffix)) return undefined
  if (subpath.length < prefix.length + suffix.length) return undefined
  return {
    key: exportKey,
    target,
    capture: subpath.slice(prefix.length, subpath.length - suffix.length),
    prefixLength: prefix.length,
    suffixLength: suffix.length,
    order
  }
}

/** Pin-scoped implementation of Node's exact-before-best-pattern selection. */
const resolveExport = (
  exportsMap: Record<string, string | null>,
  subpath: string
): { key: string; target: string | null } | undefined => {
  if (Object.prototype.hasOwnProperty.call(exportsMap, subpath)) {
    return { key: subpath, target: exportsMap[subpath] ?? null }
  }

  const matches: Array<PatternMatch> = []
  Object.entries(exportsMap).forEach(([key, target], order) => {
    const match = matchPattern(key, target, subpath, order)
    if (match !== undefined) matches.push(match)
  })
  matches.sort((left, right) =>
    right.prefixLength - left.prefixLength ||
    right.suffixLength - left.suffixLength ||
    right.key.length - left.key.length ||
    left.order - right.order)
  const winner = matches[0]
  if (winner === undefined) return undefined
  return {
    key: winner.key,
    target: winner.target === null ? null : winner.target.replaceAll("*", winner.capture)
  }
}

const reversePattern = (
  exportKey: string,
  targetPattern: string,
  packageFile: string
): string | undefined => {
  const keyStar = exportKey.indexOf("*")
  const targetStar = targetPattern.indexOf("*")
  if (keyStar < 0 || targetStar < 0) return undefined
  const targetPrefix = targetPattern.slice(0, targetStar)
  const targetSuffix = targetPattern.slice(targetStar + 1)
  if (!packageFile.startsWith(targetPrefix) || !packageFile.endsWith(targetSuffix)) {
    return undefined
  }
  const capture = packageFile.slice(
    targetPrefix.length,
    packageFile.length - targetSuffix.length
  )
  return exportKey.replaceAll("*", capture)
}

const existsIn = (files: ReadonlySet<string>, packagePath: string): boolean =>
  files.has(packagePath.startsWith("./") ? packagePath.slice(2) : packagePath)

const classifyStability = (specifier: string): PublicEntry["stability"] =>
  specifier === "effect/testing" || specifier.startsWith("effect/testing/")
    ? "testing"
    : specifier === "effect/unstable" || specifier.startsWith("effect/unstable/")
      ? "unstable"
      : "stable"

const enumeratePublicEntries = (
  packageInfo: PackageInfo,
  allFiles: ReadonlyArray<string>
): {
  entries: ReadonlyArray<PublicEntry>
  nullMaskedCandidates: ReadonlyArray<string>
  unmatchedJsFiles: ReadonlyArray<string>
} => {
  const packageFiles = allFiles.map(packageRelative)
  const packageFileSet = new Set(packageFiles)
  const jsTargets = packageFiles.filter((path) => path.startsWith("dist/") && path.endsWith(".js"))
  const candidates = new Set<string>()

  for (const [key, target] of Object.entries(packageInfo.exports)) {
    if (!key.includes("*")) candidates.add(key)
    if (target === null || !key.includes("*") || !target.includes("*")) continue
    for (const js of jsTargets) {
      const candidate = reversePattern(key, target, `./${js}`)
      if (candidate !== undefined) candidates.add(candidate)
    }
  }

  const rows: Array<PublicEntry> = []
  const nullMasked: Array<string> = []
  for (const subpath of [...candidates].sort(compareText)) {
    const resolved = resolveExport(packageInfo.exports, subpath)
    if (resolved === undefined) continue
    if (resolved.target === null) {
      nullMasked.push(subpath)
      continue
    }
    if (!resolved.target.endsWith(".js")) continue
    if (!existsIn(packageFileSet, resolved.target)) continue

    const declaration = resolved.target.replace(/\.js$/, ".d.ts")
    const source = resolved.target.replace(/^\.\/dist\//, "./src/").replace(/\.js$/, ".ts")
    const publicName = subpath === "." ? packageInfo.name : `${packageInfo.name}/${subpath.slice(2)}`
    const segments = subpath.slice(2).split("/")
    rows.push({
      specifier: publicName,
      exportKey: resolved.key,
      js: resolved.target.slice(2),
      declaration: declaration.slice(2),
      source: source.slice(2),
      hasDeclaration: existsIn(packageFileSet, declaration),
      hasSource: existsIn(packageFileSet, source),
      containsInternalSegment: segments.includes("internal"),
      stability: classifyStability(publicName)
    })
  }

  rows.sort((left, right) => compareText(left.specifier, right.specifier))
  const resolvedTargets = new Set(rows.map((row) => row.js))
  const unmatchedJsFiles = jsTargets
    .filter((path) => !resolvedTargets.has(path))
    .sort(compareText)
  return {
    entries: rows,
    nullMaskedCandidates: nullMasked.sort(compareText),
    unmatchedJsFiles
  }
}

const declarationCoordinate = (declaration: ts.Declaration): DeclarationCoordinate => {
  const sourceFile = declaration.getSourceFile()
  const start = declaration.getStart(sourceFile, false)
  const lineColumn = sourceFile.getLineAndCharacterOfPosition(start)
  return {
    file: packageRelative(sourceFile.fileName),
    syntaxKind: ts.SyntaxKind[declaration.kind] ?? `SyntaxKind(${declaration.kind})`,
    start,
    end: declaration.getEnd(),
    line: lineColumn.line + 1,
    column: lineColumn.character + 1
  }
}

const compareDeclaration = (left: DeclarationCoordinate, right: DeclarationCoordinate): number =>
  compareText(left.file, right.file) ||
  left.start - right.start ||
  left.end - right.end ||
  compareText(left.syntaxKind, right.syntaxKind)

const symbolSpaces = (symbol: ts.Symbol): ReadonlyArray<ExposureCoordinate["space"]> => {
  const spaces: Array<ExposureCoordinate["space"]> = []
  const flags = symbol.getFlags()
  if ((flags & ts.SymbolFlags.Type) !== 0) spaces.push("type")
  if ((flags & ts.SymbolFlags.Value) !== 0) spaces.push("value")
  if ((flags & ts.SymbolFlags.Namespace) !== 0) spaces.push("namespace")
  return spaces
}

const stableEntries = (entries: ReadonlyArray<PublicEntry>): ReadonlyArray<PublicEntry> =>
  entries.filter((row) =>
    row.stability === "stable" &&
    !row.containsInternalSegment &&
    (row.specifier === "effect" || row.specifier.split("/").length === 2))

const censusStableCoordinates = (
  packageInfo: PackageInfo,
  entries: ReadonlyArray<PublicEntry>
): {
  exposures: ReadonlyArray<ExposureCoordinate>
  canonical: ReadonlyArray<CanonicalCoordinate>
  programSourceFiles: number
  diagnostics: ReadonlyArray<string>
} => {
  const stable = stableEntries(entries)
  const rootNames = stable.map((row) => join(EFFECT_ROOT, row.declaration))
  const options: ts.CompilerOptions = {
    allowImportingTsExtensions: true,
    module: ts.ModuleKind.ESNext,
    moduleResolution: ts.ModuleResolutionKind.Bundler,
    noEmit: true,
    skipLibCheck: true,
    strict: true,
    target: ts.ScriptTarget.ESNext,
    types: []
  }
  const program = ts.createProgram({ rootNames, options })
  const checker = program.getTypeChecker()
  const diagnostics = ts.getPreEmitDiagnostics(program)
    .filter((diagnostic) => diagnostic.category === ts.DiagnosticCategory.Error)
    .map((diagnostic) => {
      const message = ts.flattenDiagnosticMessageText(diagnostic.messageText, "\n")
      if (diagnostic.file === undefined || diagnostic.start === undefined) return message
      const point = diagnostic.file.getLineAndCharacterOfPosition(diagnostic.start)
      return `${normalizeSlash(diagnostic.file.fileName)}:${point.line + 1}:${point.character + 1}: ${message}`
    })
    .sort(compareText)

  const exposures: Array<ExposureCoordinate> = []
  for (const entry of stable) {
    const sourceFile = program.getSourceFile(join(EFFECT_ROOT, entry.declaration))
    if (sourceFile === undefined) throw new Error(`declaration root not loaded: ${entry.declaration}`)
    const moduleSymbol = checker.getSymbolAtLocation(sourceFile)
    if (moduleSymbol === undefined) throw new Error(`module symbol missing: ${entry.declaration}`)
    const moduleExports = checker.getExportsOfModule(moduleSymbol)
      .sort((left, right) => compareText(left.getName(), right.getName()))

    for (const exported of moduleExports) {
      const target = (exported.getFlags() & ts.SymbolFlags.Alias) !== 0
        ? checker.getAliasedSymbol(exported)
        : exported
      const declarations = (target.getDeclarations() ?? exported.getDeclarations() ?? [])
        .map(declarationCoordinate)
        .sort(compareDeclaration)
      for (const space of symbolSpaces(target)) {
        const exportPath = exported.getName()
        exposures.push({
          key: `${entry.specifier}::${exportPath}::${space}`,
          module: entry.specifier,
          exportPath,
          space,
          declarations
        })
      }
    }
  }
  exposures.sort((left, right) => compareText(left.key, right.key))

  const groups = new Map<string, Array<ExposureCoordinate>>()
  for (const exposure of exposures) {
    const declarationSet = exposure.declarations
      .map((declaration) => `${declaration.file}:${declaration.syntaxKind}:${declaration.start}:${declaration.end}`)
    const identity = `${exposure.space}\u0000${declarationSet.join("\u0000")}`
    const group = groups.get(identity)
    if (group === undefined) groups.set(identity, [exposure])
    else group.push(exposure)
  }

  const canonical: Array<CanonicalCoordinate> = []
  for (const group of groups.values()) {
    group.sort((left, right) => {
      const leftDirect = left.declarations.some((declaration) =>
        declaration.file === entries.find((entry) => entry.specifier === left.module)?.declaration)
      const rightDirect = right.declarations.some((declaration) =>
        declaration.file === entries.find((entry) => entry.specifier === right.module)?.declaration)
      return Number(rightDirect) - Number(leftDirect) ||
        left.module.length - right.module.length ||
        left.exportPath.length - right.exportPath.length ||
        compareText(left.key, right.key)
    })
    const chosen = group[0]
    if (chosen === undefined) throw new Error("empty canonical coordinate group")
    canonical.push({
      key: `${packageInfo.name}@${packageInfo.version}::${chosen.module}::${chosen.exportPath}::${chosen.space}`,
      module: chosen.module,
      exportPath: chosen.exportPath,
      space: chosen.space,
      declarations: chosen.declarations,
      exposures: group.map((row) => row.key).sort(compareText)
    })
  }
  canonical.sort((left, right) => compareText(left.key, right.key))

  return {
    exposures,
    canonical,
    programSourceFiles: program.getSourceFiles().length,
    diagnostics
  }
}

const duplicateKeys = (keys: ReadonlyArray<string>): ReadonlyArray<string> => {
  const seen = new Set<string>()
  const duplicates = new Set<string>()
  for (const key of keys) {
    if (seen.has(key)) duplicates.add(key)
    seen.add(key)
  }
  return [...duplicates].sort(compareText)
}

const main = (): { output: JsonRecord; failed: boolean } => {
  const packageInfo = parsePackage(readFileSync(PACKAGE_JSON, "utf8"))
  const allFiles = walkFiles(EFFECT_ROOT)
  const oldBankModules = parseOldBankModules(readFileSync(OLD_BANK, "utf8"))
  const oldBankSet = new Set(oldBankModules)
  const publicCensus = enumeratePublicEntries(packageInfo, allFiles)
  const publicEntries = publicCensus.entries
  const codeSet = new Set(publicEntries.map((entry) => entry.specifier))
  const coordinates = censusStableCoordinates(packageInfo, publicEntries)

  const exposureDuplicates = duplicateKeys(coordinates.exposures.map((row) => row.key))
  const canonicalDuplicates = duplicateKeys(coordinates.canonical.map((row) => row.key))
  const moduleDuplicates = duplicateKeys(publicEntries.map((row) => row.specifier))
  const missingPairs = publicEntries
    .filter((row) => !row.hasDeclaration || !row.hasSource)
    .map((row) => row.specifier)
    .sort(compareText)

  const sentinelRows = SENTINELS.map((specifier) => {
    const row = publicEntries.find((entry) => entry.specifier === specifier)
    return {
      specifier,
      public: codeSet.has(specifier),
      hasDeclaration: row?.hasDeclaration ?? false,
      hasSource: row?.hasSource ?? false,
      absentFromOldBank: !oldBankSet.has(specifier)
    }
  })

  const failures: Array<string> = []
  if (packageInfo.name !== "effect") failures.push(`unexpected package name ${packageInfo.name}`)
  if (moduleDuplicates.length > 0) failures.push("duplicate public module keys")
  if (exposureDuplicates.length > 0) failures.push("duplicate stable exposure keys")
  if (canonicalDuplicates.length > 0) failures.push("duplicate canonical surface keys")
  if (missingPairs.length > 0) failures.push("public code entries missing declaration/source pairs")
  if (coordinates.diagnostics.length > 0) failures.push("TypeScript declaration program has errors")
  for (const sentinel of sentinelRows) {
    if (!sentinel.public || !sentinel.hasDeclaration || !sentinel.hasSource) {
      failures.push(`missing public sentinel ${sentinel.specifier}`)
    }
    if (!sentinel.absentFromOldBank) failures.push(`old bank unexpectedly contains ${sentinel.specifier}`)
  }

  const shippedJs = allFiles
    .map(packageRelative)
    .filter((path) => path.startsWith("dist/") && path.endsWith(".js"))
  const nonInternalEntries = publicEntries.filter((row) => !row.containsInternalSegment)
  const internalEntries = publicEntries.filter((row) => row.containsInternalSegment)
  const stable = stableEntries(publicEntries)
  const output: JsonRecord = {
    schemaVersion: "foldlab.effect-surface-probe.v1",
    status: failures.length === 0 ? "ok" : "error",
    instrument: {
      name: "typescript",
      version: ts.version,
      role: "declaration syntax/type coordinate instrument; no semantic Effect claim"
    },
    package: {
      name: packageInfo.name,
      version: packageInfo.version,
      exportsRules: Object.keys(packageInfo.exports).length
    },
    counts: {
      shippedPackageFiles: allFiles.length,
      shippedJsFiles: shippedJs.length,
      resolvedCodeEntries: publicEntries.length,
      resolvedNonInternalCodeEntries: nonInternalEntries.length,
      resolvedInternalNamedCodeEntries: internalEntries.length,
      stableDirectCodeEntriesIncludingRoot: stable.length,
      stableDirectModulesExcludingRoot: stable.filter((row) => row.specifier !== "effect").length,
      nullMaskedCandidates: publicCensus.nullMaskedCandidates.length,
      unmatchedJsFiles: publicCensus.unmatchedJsFiles.length,
      oldBankModules: oldBankModules.length,
      typescriptProgramSourceFiles: coordinates.programSourceFiles,
      stableExposureCoordinates: coordinates.exposures.length,
      stableCanonicalCoordinates: coordinates.canonical.length,
      typescriptErrors: coordinates.diagnostics.length
    },
    sentinels: sentinelRows,
    checks: {
      duplicatePublicModuleKeys: moduleDuplicates,
      duplicateStableExposureKeys: exposureDuplicates,
      duplicateCanonicalSurfaceKeys: canonicalDuplicates,
      missingDeclarationOrSourcePairs: missingPairs,
      typescriptErrors: coordinates.diagnostics,
      failures
    },
    digests: {
      publicEntries: sha256(publicEntries),
      nonInternalEntries: sha256(nonInternalEntries),
      stableExposureCoordinates: sha256(coordinates.exposures),
      stableCanonicalCoordinates: sha256(coordinates.canonical)
    }
  }
  if (SUMMARY_ONLY) {
    output.mode = "summary"
    output.boundaries = {
      firstPublicEntry: publicEntries[0]?.specifier ?? null,
      lastPublicEntry: publicEntries.at(-1)?.specifier ?? null,
      firstStableCoordinate: coordinates.canonical[0]?.key ?? null,
      lastStableCoordinate: coordinates.canonical.at(-1)?.key ?? null,
      acceptedInternalNamedExamples: internalEntries.slice(0, 5).map((row) => row.specifier),
      unmatchedJsExamples: publicCensus.unmatchedJsFiles.slice(0, 5)
    }
  } else {
    output.mode = "full"
    output.publicEntries = publicEntries
    output.nullMaskedCandidates = publicCensus.nullMaskedCandidates
    output.unmatchedJsFiles = publicCensus.unmatchedJsFiles
    output.stableExposureCoordinates = coordinates.exposures
    output.stableCanonicalCoordinates = coordinates.canonical
  }
  return { output, failed: failures.length > 0 }
}

try {
  const result = main()
  process.stdout.write(`${JSON.stringify(result.output, null, 2)}\n`)
  if (result.failed) process.exitCode = 1
} catch (error: unknown) {
  const message = error instanceof Error ? error.message : String(error)
  process.stdout.write(`${JSON.stringify({
    schemaVersion: "foldlab.effect-surface-probe.v1",
    status: "error",
    fatal: message
  }, null, 2)}\n`)
  process.exitCode = 1
}
