/** Pinned TypeScript diagnostics for explicitly selected program/adapter type claims.
 * Assignment statements are the comparison; typeToString is display data only. */
import * as ts from "../../ts/eff/node_modules/typescript/lib/typescript.js"
import { createHash } from "node:crypto"
import { existsSync, readFileSync } from "node:fs"
import { join, relative, resolve } from "node:path"

export type Axis = "A" | "E" | "R" | "request" | "receiver"
export interface Issue { code: string; message: string; axis?: Axis }
export interface Query {
  id: string
  source: string
  /** Import declarations and explicit bindings; no value assertions are generated. */
  imports: string[]
  subject: string
  kind: "effect" | "function"
  receiver?: string
  expected: Partial<Record<Axis, string>>
  allowUnknown?: Axis[]
  inputIssues?: Issue[]
  provenance?: unknown
}
export interface Diagnostic {
  code: number; file: string; line: number; column: number; message: string
}
export interface Column {
  expected: string | null; actual: string | null
  actualToExpected: boolean | null; expectedToActual: boolean | null
}
export interface Observation {
  id: string; source: string; status: "agree" | "mismatch" | "refused"
  binding: { subject: string; receiver: string | null; imports: string[]; unknownPolicy: Axis[] }
  columns: Partial<Record<Axis, Column>>
  issues: Issue[]; diagnostics: Diagnostic[]
  signatures: Array<{ text: string; parameters: Array<{ name: string; type: string; optional: boolean; rest: boolean }> }>
  provenance: unknown
}
export interface Report {
  format: "effect4-target-report-v1"
  profile: string
  versions: { typescript: string; effect: string; lean: string }
  compilerOptions: unknown
  expected: string[]; attempted: string[]; resolved: string[]; mismatching: string[]; refused: string[]
  globalDiagnostics: Diagnostic[]; observations: Observation[]
  sourceHashes: Record<string, string>
  limitations: string[]
  conforms: boolean
}

const hash = (s: string) => createHash("sha256").update(s).digest("hex")
const axes: Axis[] = ["A", "E", "R", "request", "receiver"]
const localPath = (repo: string, path: string) => relative(repo, path).replaceAll("\\", "/")
const stableText = (repo: string, text: string) => text.replaceAll(repo, "<repo>")
const bindingName = (axis: Axis, direction: string) => `__${axis}_${direction}`

function querySource(q: Query): string {
  const lines = [
    'import type * as Effect from "effect/Effect"', ...q.imports,
    `type __Subject = ${q.subject}`,
    `type __Effect = ${q.kind === "function" ? "ReturnType<__Subject>" : "__Subject"}`,
    "type __EffectShape = [__Effect] extends [never] ? false : __Effect extends Effect.Effect<infer _A, infer _E, infer _R> ? true : false",
    "declare const __effectShape: __EffectShape",
    "export const __requiresEffect: true = __effectShape",
    "type __Actual_A = Effect.Success<__Effect>",
    "type __Actual_E = Effect.Error<__Effect>",
    "type __Actual_R = Effect.Services<__Effect>",
  ]
  if (q.kind === "function") lines.push("type __Actual_request = Parameters<__Subject>")
  if (q.receiver !== undefined) lines.push(`type __Actual_receiver = ${q.receiver}`)
  for (const axis of axes) {
    if ((axis === "request" && q.kind !== "function") || (axis === "receiver" && q.receiver === undefined)) continue
    lines.push(`declare const __${axis}_actual: __Actual_${axis}`)
    const expected = q.expected[axis]
    if (expected === undefined) continue
    lines.push(`type __Expected_${axis} = ${expected}`,
      `declare const __${axis}_expected: __Expected_${axis}`,
      `export const ${bindingName(axis, "actualToExpected")}: __Expected_${axis} = __${axis}_actual`,
      `export const ${bindingName(axis, "expectedToActual")}: __Actual_${axis} = __${axis}_expected`)
  }
  return lines.join("\n") + "\n"
}

/** Reject any/unknown in compared data positions, including nested containers and fields.
 * Call signatures are checked as parameter/result columns, not by traversing a class's methods. */
function forbiddenTypes(checker: ts.TypeChecker, root: ts.Type, allowUnknown: boolean): string[] {
  const seen = new Set<ts.Type>(), found = new Set<string>()
  const visit = (type: ts.Type) => {
    if (seen.has(type)) return
    seen.add(type)
    if (seen.size > 4000) { found.add("inspection-limit"); return }
    if (type.flags & ts.TypeFlags.Any) { found.add("any"); return }
    if (type.flags & ts.TypeFlags.Unknown) { if (!allowUnknown) found.add("unknown"); return }
    if (type.isUnionOrIntersection()) { type.types.forEach(visit); return }
    if (!(type.flags & ts.TypeFlags.Object)) return
    type.aliasTypeArguments?.forEach(visit)
    if ((type as ts.ObjectType).objectFlags & ts.ObjectFlags.Reference) {
      checker.getTypeArguments(type as ts.TypeReference).forEach(visit)
    }
    if (checker.getSignaturesOfType(type, ts.SignatureKind.Call).length) return
    // Generic payloads above remain inspected. Library implementation fields and adapter
    // class internals are opaque; the assignment checks still compare their public types.
    const symbol = type.getSymbol()
    if (symbol && ((symbol.flags & ts.SymbolFlags.Class) || symbol.declarations?.some(d => d.getSourceFile().fileName.replaceAll("\\", "/").includes("/node_modules/")))) return
    // Arrays/tuples were covered through type arguments; their built-in methods are not data.
    if (checker.isArrayType(type) || checker.isTupleType(type)) return
    for (const property of checker.getPropertiesOfType(type)) {
      const declaration = property.valueDeclaration ?? property.declarations?.[0]
      if (declaration) visit(checker.getTypeOfSymbolAtLocation(property, declaration))
    }
  }
  visit(root)
  return [...found].sort()
}

export function query(repoRoot: string, queries: readonly Query[], profile = "effect@4.0.0-rc.112/adapter"): Report {
  const repo = resolve(repoRoot)
  if (new Set(queries.map(q => q.id)).size !== queries.length) throw new Error("duplicate target query ID")
  if (!queries.length) throw new Error("empty required target selection")
  const configFile = join(repo, "ts/eff/tsconfig.json")
  const config = ts.readConfigFile(configFile, ts.sys.readFile)
  if (config.error) throw new Error(ts.flattenDiagnosticMessageText(config.error.messageText, " "))
  const parsed = ts.parseJsonConfigFileContent(config.config, ts.sys, join(repo, "ts/eff"))
  if (parsed.errors.length) throw new Error(parsed.errors.map(d => ts.flattenDiagnosticMessageText(d.messageText, " ")).join("\n"))
  const options = { ...parsed.options, noEmit: true, typeRoots: [join(repo, "ts/eff/node_modules/@types")] }
  const virtual = new Map<string, string>()
  const fileOf = new Map<string, string>()
  queries.forEach((q, index) => {
    const file = join(repo, "ts/eff/__target_queries__", `q${index}.ts`)
    virtual.set(file, querySource(q)); fileOf.set(q.id, file)
  })
  const host = ts.createCompilerHost(options)
  const read = host.readFile.bind(host), fileExists = host.fileExists.bind(host)
  host.readFile = file => virtual.get(file) ?? read(file)
  host.fileExists = file => virtual.has(file) || fileExists(file)
  host.getSourceFile = (file, languageVersion) => {
    const text = host.readFile(file)
    return text === undefined ? undefined : ts.createSourceFile(file, text, languageVersion, true)
  }
  const program = ts.createProgram([...virtual.keys()], options, host)
  const checker = program.getTypeChecker()
  const allDiagnostics = ts.getPreEmitDiagnostics(program)
  const diagnostic = (d: ts.Diagnostic): Diagnostic => {
    const position = d.file && d.start !== undefined ? d.file.getLineAndCharacterOfPosition(d.start) : undefined
    return { code: d.code, file: d.file ? localPath(repo, d.file.fileName) : "<compiler>",
      line: position ? position.line + 1 : 0, column: position ? position.character + 1 : 0,
      message: stableText(repo, ts.flattenDiagnosticMessageText(d.messageText, " ")) }
  }
  const globals = allDiagnostics.filter(d => !d.file || !virtual.has(d.file.fileName))
  const observations: Observation[] = queries.map(q => {
    const file = fileOf.get(q.id)!
    const sf = program.getSourceFile(file)
    const issues: Issue[] = [...q.inputIssues ?? []]
    if (!existsSync(resolve(repo, q.source))) issues.push({ code: "missing-source", message: q.source })
    if (!sf) issues.push({ code: "missing-query-source", message: q.id })
    if (globals.length) issues.push({ code: "dependency-diagnostic", message: "Compiler diagnostics in imported inputs; see globalDiagnostics" })
    const columns: Observation["columns"] = {}
    const variables = new Map<string, ts.Identifier>(), aliases = new Map<string, ts.TypeAliasDeclaration>()
    const walk = (node: ts.Node) => {
      if (ts.isVariableDeclaration(node) && ts.isIdentifier(node.name)) variables.set(node.name.text, node.name)
      if (ts.isTypeAliasDeclaration(node)) aliases.set(node.name.text, node)
      ts.forEachChild(node, walk)
    }
    if (sf) walk(sf)
    const ds = allDiagnostics.filter(d => d.file?.fileName === file)
    const onAssignment = (d: ts.Diagnostic, axis: Axis, direction: string) => {
      const id = variables.get(bindingName(axis, direction))
      return id !== undefined && d.start !== undefined && d.start >= id.parent.getStart() && d.start < id.parent.end
    }
    const otherDiagnostics = ds.filter(d => !axes.some(axis => ["actualToExpected", "expectedToActual"].some(direction => onAssignment(d, axis, direction))))
    if (otherDiagnostics.length) issues.push({ code: "query-diagnostic", message: "Unresolved or invalid query/type binding; see diagnostics" })
    const textOf = (type: ts.Type, at: ts.Node) => checker.typeToString(type, at, ts.TypeFormatFlags.NoTruncation | ts.TypeFormatFlags.InTypeAlias)
    for (const axis of axes) {
      const actual = variables.get(`__${axis}_actual`)
      if (!actual) continue
      const expected = variables.get(`__${axis}_expected`)
      const actualType = checker.getTypeAtLocation(actual)
      const column: Column = { actual: textOf(actualType, actual), expected: q.expected[axis] ?? null,
        actualToExpected: null, expectedToActual: null }
      columns[axis] = column
      if (!expected) issues.push({ code: "missing-type-metadata", axis, message: `Missing expected ${axis}` })
      for (const [side, type] of [["actual", actualType], ...(expected ? [["expected", checker.getTypeAtLocation(expected)] as const] : [])] as const) {
        for (const kind of forbiddenTypes(checker, type, q.allowUnknown?.includes(axis) ?? false)) {
          issues.push({ code: `unresolved-${kind}`, axis, message: `${side} ${axis} contains ${kind}` })
        }
      }
      if (expected && !globals.length && !otherDiagnostics.length && !issues.some(i => i.axis === axis)) {
        column.actualToExpected = !ds.some(d => onAssignment(d, axis, "actualToExpected"))
        column.expectedToActual = !ds.some(d => onAssignment(d, axis, "expectedToActual"))
      }
    }
    const signatures: Observation["signatures"] = []
    if (q.kind === "function") {
      const subject = aliases.get("__Subject")
      const type = subject && checker.getTypeAtLocation(subject)
      const found = type ? checker.getSignaturesOfType(type, ts.SignatureKind.Call) : []
      for (const signature of found) {
        signatures.push({ text: checker.signatureToString(signature, subject, ts.TypeFormatFlags.NoTruncation),
          parameters: signature.getParameters().map(parameter => {
            const declaration = parameter.valueDeclaration ?? parameter.declarations?.[0]
            return { name: parameter.name,
              type: declaration ? textOf(checker.getTypeOfSymbolAtLocation(parameter, declaration), declaration) : "<missing>",
              optional: !!(parameter.flags & ts.SymbolFlags.Optional) || !!(declaration && ts.isParameter(declaration) && (declaration.questionToken || declaration.initializer)),
              rest: !!(declaration && ts.isParameter(declaration) && declaration.dotDotDotToken) }
          }) })
      }
      if (found.length !== 1) issues.push({ code: "unsupported-overloads", message: `Expected one concrete signature, found ${found.length}; signatures retained` })
      if (found.some(s => s.typeParameters?.length)) issues.push({ code: "unsupported-generic-signature", message: "Generic member requires an explicit instantiation query" })
    }
    const mismatch = Object.values(columns).some(c => c.actualToExpected === false || c.expectedToActual === false)
    return { id: q.id, source: q.source, status: issues.length ? "refused" : mismatch ? "mismatch" : "agree",
      binding: { subject: q.subject, receiver: q.receiver ?? null, imports: q.imports.map(i => stableText(repo, i)), unknownPolicy: q.allowUnknown ?? [] },
      columns, issues, diagnostics: ds.map(diagnostic), signatures, provenance: q.provenance ?? null }
  })
  const sourceHashes: Record<string, string> = {}
  for (const sf of [...program.getSourceFiles()].sort((a, b) => a.fileName.localeCompare(b.fileName))) {
    sourceHashes[localPath(repo, sf.fileName)] = hash(stableText(repo, sf.text))
  }
  const packageVersion = (name: string) => {
    const file = join(repo, "ts/eff/node_modules", name, "package.json")
    const text = readFileSync(file, "utf8")
    sourceHashes[localPath(repo, file)] = hash(text)
    const value: unknown = JSON.parse(text)
    if (!value || typeof value !== "object" || !("version" in value) || typeof value.version !== "string") throw new Error(`${name}: missing package version`)
    return value.version
  }
  sourceHashes["ts/eff/tsconfig.json"] = hash(readFileSync(configFile, "utf8"))
  sourceHashes["lean-toolchain"] = hash(readFileSync(join(repo, "lean-toolchain"), "utf8"))
  const report: Report = { format: "effect4-target-report-v1", profile,
    versions: { typescript: packageVersion("typescript"), effect: packageVersion("effect"), lean: readFileSync(join(repo, "lean-toolchain"), "utf8").trim() },
    compilerOptions: { ...config.config.compilerOptions, typeRoots: ["<repo>/ts/eff/node_modules/@types"] },
    expected: queries.map(q => q.id), attempted: observations.map(o => o.id),
    resolved: observations.filter(o => o.status !== "refused").map(o => o.id),
    mismatching: observations.filter(o => o.status === "mismatch").map(o => o.id),
    refused: observations.filter(o => o.status === "refused").map(o => o.id),
    globalDiagnostics: globals.map(diagnostic), observations, sourceHashes,
    limitations: ["Finite TypeScript mutual assignability under explicit target bindings; no Lean semantic equivalence claim.",
      "Requirement carrier equality does not establish Lean service-key identity.",
      "Any/unknown inspection covers compared roots, generic payloads and local record fields; library implementation fields and class internals are opaque."],
    conforms: !globals.length && observations.every(o => o.status === "agree") }
  if (report.versions.typescript !== ts.version) throw new Error("loaded TypeScript differs from selected repository pin")
  return report
}
