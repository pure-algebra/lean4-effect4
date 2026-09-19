/** The oracle's compiler side: the one compiler (tsgo) answering one request file.
 *
 *     node tools/target/checker.ts <request.json> <response.json>
 *
 * node, not bun: the compiler's synchronous client reads a node-internal pipe handle, the same
 * reason `harness/tsdiag/run-tsdiag.mjs` is node. `oracle.ts` is the face that runs this and
 * holds the types and the query sources; nothing else in the repository drives a type checker.
 *
 * The query modules are never written to disk: the compiler reads them through its virtual
 * filesystem callbacks, beside `ts/eff/tsconfig.json`, so they resolve `effect` and the
 * adapter exactly as the package's own sources do.
 */
import { createHash } from "node:crypto"
import { existsSync, readFileSync, writeFileSync } from "node:fs"
import { isAbsolute, join, relative, resolve } from "node:path"
import {
  API, NodeBuilderFlags, type Project, SignatureKind, SymbolFlags, type Type, TypeFlags,
} from "../../ts/eff/node_modules/@typescript/native-preview/dist/api/sync/api.js"
import type { Diagnostic as CompilerDiagnostic } from "../../ts/eff/node_modules/@typescript/native-preview/dist/api/sync/types.js"
import type { Node, SourceFile } from "../../ts/eff/node_modules/@typescript/native-preview/dist/ast/index.js"
import {
  isIdentifier, isIndexedAccessTypeNode, isParameterDeclaration, isTypeAliasDeclaration, isVariableDeclaration, SyntaxKind,
} from "../../ts/eff/node_modules/@typescript/native-preview/dist/ast/index.js"
import {
  bindingName, querySource,
  type Axis, type Column, type Diagnostic, type Issue, type Observation, type Query, type Report,
} from "./oracle.ts"

const COMPILER = "@typescript/native-preview"
const axes: Axis[] = ["A", "E", "R", "request", "receiver"]
const hash = (s: string) => createHash("sha256").update(s).digest("hex")
const localPath = (repo: string, path: string) => relative(repo, path).replaceAll("\\", "/")
const stableText = (repo: string, text: string) => text.replaceAll(repo, "<repo>")
// The compiler's assignment incompatibilities, including missing object properties and exact
// optional properties. Every other diagnostic remains a refusal, even on a binding.
const assignmentDiagnostics = new Set([2322, 2375, 2739, 2740, 2741])
const formatFlags = NodeBuilderFlags.NoTruncation | NodeBuilderFlags.InTypeAlias

/** The compiler this repository pins, and the refusal when the install is not the manifest's. */
function compilerVersion(repo: string): string {
  const manifest = JSON.parse(readFileSync(join(repo, "ts/eff/package.json"), "utf8")) as
    { devDependencies?: Record<string, string> }
  const pinned = manifest.devDependencies?.[COMPILER]
  const installed = (JSON.parse(readFileSync(join(repo, "ts/eff/node_modules", COMPILER, "package.json"), "utf8")) as
    { version: string }).version
  if (pinned !== installed) throw new Error(`target oracle: ${COMPILER} ${installed} is installed, ts/eff/package.json pins ${pinned}`)
  return installed
}

/** One compiler instance over a virtual project beside `ts/eff/tsconfig.json`. */
function open(repo: string, directory: string, sources: ReadonlyMap<string, string>, options: Record<string, unknown>) {
  const names = [...sources.keys()]
  const files = new Map(sources)
  files.set(join(directory, "tsconfig.json"), JSON.stringify({
    extends: "../tsconfig.json", compilerOptions: options, include: [], files: names,
  }))
  const entries = { files: [...files.keys()].map(f => localPath(directory, f)), directories: [] }
  const api = new API({
    cwd: join(repo, "ts/eff"),
    fs: {
      fileExists: file => (files.has(file) ? true : undefined),
      readFile: file => files.get(file),
      directoryExists: dir => (dir === directory ? true : undefined),
      getAccessibleEntries: dir => (dir === directory ? entries : undefined),
      realpath: path => (files.has(path) || path === directory ? path : undefined),
    },
  })
  const snapshot = api.updateSnapshot({ openProjects: [join(directory, "tsconfig.json")] })
  const project = snapshot.getProjects()[0]
  if (!project) throw new Error("target oracle: the compiler opened no project")
  return { api, project, files }
}

/** Every declared name of a module, by kind: the bindings the verdicts are read at. */
function names(file: SourceFile) {
  const variables = new Map<string, Node>(), aliases = new Map<string, Node>()
  const walk = (node: Node) => {
    if (isVariableDeclaration(node) && isIdentifier(node.name)) variables.set(node.name.text, node.name)
    if (isTypeAliasDeclaration(node)) aliases.set(node.name.text, node)
    node.forEachChild(walk)
  }
  file.forEachChild(walk)
  return { variables, aliases }
}

const lineAndColumn = (text: string, position: number) => {
  const before = text.slice(0, Math.max(0, position))
  const line = before.split("\n").length
  return { line, column: position - (before.lastIndexOf("\n") + 1) + 1 }
}

/** Reject any/unknown in compared data positions, including nested containers and fields.
 * Call signatures are checked as parameter/result columns, not by traversing a class's methods.
 * The answer is a function of the root type and the policy, and every question of the compiler
 * is a synchronous round trip, so one program's answers are kept. */
const inspected = new Map<string, string[]>()
function forbiddenTypes(project: Project, root: Type, allowUnknown: boolean): string[] {
  const memo = `${root.id}:${allowUnknown}`
  const kept = inspected.get(memo)
  if (kept) return kept
  const checker = project.checker
  const seen = new Set<number>(), found = new Set<string>()
  const visit = (type: Type) => {
    if (seen.has(type.id)) return
    seen.add(type.id)
    if (seen.size > 4000) { found.add("inspection-limit"); return }
    if (type.flags & TypeFlags.Any) { found.add("any"); return }
    if (type.flags & TypeFlags.Unknown) { if (!allowUnknown) found.add("unknown"); return }
    if (type.isUnionType() || type.isIntersectionType()) { type.getTypes().forEach(visit); return }
    if (!(type.flags & TypeFlags.Object)) return
    type.getAliasTypeArguments().forEach(visit)
    // Only a reference has type arguments; asking any other type crashes the compiler's server.
    if (type.isTypeReference()) checker.getTypeArguments(type).forEach(visit)
    if (checker.getSignaturesOfType(type, SignatureKind.Call).length) return
    // Generic payloads above remain inspected. Library implementation fields and adapter
    // class internals are opaque; the assignment checks still compare their public types.
    const symbol = type.getSymbol()
    if (symbol && ((symbol.flags & SymbolFlags.Class) ||
      symbol.declarations.some(d => String(d.path).replaceAll("\\", "/").includes("/node_modules/")))) return
    // Arrays/tuples were covered through type arguments; their built-in methods are not data.
    if (checker.isArrayType(type) || checker.isTupleType(type)) return
    for (const property of checker.getPropertiesOfType(type)) {
      const declared = checker.getTypeOfSymbol(property)
      if (declared) visit(declared)
    }
  }
  visit(root)
  const kinds = [...found].sort()
  inspected.set(memo, kinds)
  return kinds
}

function report(repo: string, profile: string, queries: readonly Query[]): Report {
  const directory = join(repo, "ts/eff/__target_queries__")
  const sources = new Map<string, string>(), fileOf = new Map<string, string>()
  queries.forEach((q, index) => {
    const file = join(directory, `q${index}.ts`)
    sources.set(file, querySource(q)); fileOf.set(q.id, file)
  })
  const version = compilerVersion(repo)
  const { api, project, files } = open(repo, directory, sources,
    { noEmit: true, typeRoots: [join(repo, "ts/eff/node_modules/@types")] })
  try {
    const { program, checker } = project
    const textOfFile = (file: string) => files.get(file) ?? (existsSync(file) ? readFileSync(file, "utf8") : "")
    const all = [...program.getConfigFileParsingDiagnostics(), ...program.getProgramDiagnostics(),
      ...program.getGlobalDiagnostics(), ...program.getSyntacticDiagnostics(), ...program.getSemanticDiagnostics()]
    const message = (d: CompilerDiagnostic): string =>
      [d.text, ...(d.messageChain ?? []).map(message)].join(" ")
    const diagnostic = (d: CompilerDiagnostic): Diagnostic => {
      const position = d.fileName ? lineAndColumn(textOfFile(d.fileName), d.pos) : undefined
      return { code: d.code, file: d.fileName ? localPath(repo, d.fileName) : "<compiler>",
        line: position ? position.line : 0, column: position ? position.column : 0,
        message: stableText(repo, message(d)) }
    }
    // A diagnostic inside a query's own source refuses that query; a diagnostic anywhere else
    // outside the virtual query files (the adapter, the package, a file no query names) refuses
    // every query. The corpus lane queries hundreds of printed modules in one program, and one
    // module that does not type must not refuse the others.
    const sourceOf = new Map(queries.map(q => [resolve(repo, q.source), q.id]))
    const inSource = all.filter(d => d.fileName && !sources.has(d.fileName) && sourceOf.has(resolve(d.fileName)))
    const globals = all.filter(d => !d.fileName || (!sources.has(d.fileName) && !sourceOf.has(resolve(d.fileName))))
    const observations: Observation[] = queries.map(q => {
      const file = fileOf.get(q.id)!
      const sf = program.getSourceFile(file)
      const issues: Issue[] = [...q.inputIssues ?? []]
      if (!existsSync(resolve(repo, q.source))) issues.push({ code: "missing-source", message: q.source })
      if (!sf) issues.push({ code: "missing-query-source", message: q.id })
      if (globals.length) issues.push({ code: "dependency-diagnostic", message: "Compiler diagnostics in imported inputs; see globalDiagnostics" })
      const own = inSource.filter(d => resolve(d.fileName!) === resolve(repo, q.source))
      if (own.length) issues.push({ code: "source-diagnostic", message: `${own.length} compiler diagnostic(s) (${[...new Set(own.map(d => `TS${d.code}`))].join(", ")}) in ${localPath(repo, resolve(repo, q.source))}: ${stableText(repo, message(own[0]!))}` })
      const columns: Observation["columns"] = {}
      const { variables, aliases } = sf ? names(sf) : { variables: new Map<string, Node>(), aliases: new Map<string, Node>() }
      const ds = all.filter(d => d.fileName === file)
      const onAssignment = (d: CompilerDiagnostic, axis: Axis, direction: string) => {
        const id = variables.get(bindingName(axis, direction))
        return id !== undefined && d.pos >= id.parent.getStart() && d.pos < id.parent.end
      }
      const otherDiagnostics = ds.filter(d => !assignmentDiagnostics.has(d.code) ||
        !axes.some(axis => ["actualToExpected", "expectedToActual"].some(direction => onAssignment(d, axis, direction))))
      if (otherDiagnostics.length) issues.push({ code: "query-diagnostic", message: "Unresolved or invalid query/type binding; see diagnostics" })
      const textOf = (type: Type, at: Node) => checker.typeToString(type, at, formatFlags)
      for (const axis of axes) {
        const actual = variables.get(`__${axis}_actual`)
        if (!actual) continue
        const expected = variables.get(`__${axis}_expected`)
        const actualType = checker.getTypeAtLocation(actual)
        const column: Column = { actual: actualType ? textOf(actualType, actual) : null, expected: q.expected[axis] ?? null,
          actualToExpected: null, expectedToActual: null, agreement: null }
        columns[axis] = column
        if (!expected) issues.push({ code: "missing-type-metadata", axis, message: `Missing expected ${axis}` })
        const expectedType = expected ? checker.getTypeAtLocation(expected) : undefined
        for (const [side, type] of [["actual", actualType], ...(expectedType ? [["expected", expectedType] as const] : [])] as const) {
          if (!type) continue
          for (const kind of forbiddenTypes(project, type, q.allowUnknown?.includes(axis) ?? false)) {
            issues.push({ code: `unresolved-${kind}`, axis, message: `${side} ${axis} contains ${kind}` })
          }
        }
        if (expected && !globals.length && !own.length && !otherDiagnostics.length && !issues.some(i => i.axis === axis)) {
          column.actualToExpected = !ds.some(d => onAssignment(d, axis, "actualToExpected"))
          column.expectedToActual = !ds.some(d => onAssignment(d, axis, "expectedToActual"))
          column.agreement = !column.actualToExpected ? "mismatch" : column.expectedToActual ? "exact" :
            q.kind === "program" && axis === "E" ? "strict-containment" : "mismatch"
        }
      }
      const signatures: Observation["signatures"] = []
      if (q.kind === "function") {
        const subject = aliases.get("__Subject")
        const type = subject && checker.getTypeAtLocation(subject)
        const found = type ? checker.getSignaturesOfType(type, SignatureKind.Call) : []
        for (const signature of found) {
          const declaration = subject && checker.signatureToSignatureDeclaration(signature, SyntaxKind.FunctionType, subject, NodeBuilderFlags.NoTruncation)
          signatures.push({ text: declaration ? project.emitter.printNode(declaration) : "<unprintable signature>",
            parameters: signature.getParameters().map((parameter, index) => {
              const handle = parameter.valueDeclaration ?? parameter.declarations[0]
              const node = handle ? handle.resolve(project) : undefined
              const type = checker.getParameterType(signature, index)
              return { name: parameter.name,
                type: type && node ? textOf(type, node) : "<missing>",
                optional: !!(parameter.flags & SymbolFlags.Optional) || !!(node && isParameterDeclaration(node) && (node.questionToken || node.initializer)),
                rest: !!(node && isParameterDeclaration(node) && node.dotDotDotToken) }
            }) })
        }
        if (found.length !== 1) issues.push({ code: "unsupported-overloads", message: `Expected one concrete signature, found ${found.length}; signatures retained` })
        if (found.some(s => s.getTypeParameters().length)) issues.push({ code: "unsupported-generic-signature", message: "Generic member requires an explicit instantiation query" })
      }
      const mismatch = Object.values(columns).some(c => c.agreement === "mismatch")
      return { id: q.id, source: q.source, status: issues.length ? "refused" : mismatch ? "mismatch" : "agree",
        binding: { kind: q.kind, subject: q.subject, receiver: q.receiver ?? null, imports: q.imports.map(i => stableText(repo, i)), unknownPolicy: q.allowUnknown ?? [] },
        columns, issues, diagnostics: ds.map(diagnostic), signatures, provenance: q.provenance ?? null }
    })
    const sourceHashes: Record<string, string> = {}
    for (const name of [...program.getSourceFileNames()].sort((a, b) => a.localeCompare(b))) {
      sourceHashes[localPath(repo, name)] = hash(stableText(repo, textOfFile(name)))
    }
    const packageVersion = (name: string) => {
      const file = join(repo, "ts/eff/node_modules", name, "package.json")
      const text = readFileSync(file, "utf8")
      sourceHashes[localPath(repo, file)] = hash(text)
      const value: unknown = JSON.parse(text)
      if (!value || typeof value !== "object" || !("version" in value) || typeof value.version !== "string") throw new Error(`${name}: missing package version`)
      return value.version
    }
    const configFile = join(repo, "ts/eff/tsconfig.json")
    sourceHashes["ts/eff/tsconfig.json"] = hash(readFileSync(configFile, "utf8"))
    sourceHashes["lean-toolchain"] = hash(readFileSync(join(repo, "lean-toolchain"), "utf8"))
    return { format: "effect4-target-report-v1", profile,
      versions: { compiler: COMPILER, typescript: packageVersion(COMPILER), effect: packageVersion("effect"),
        lean: readFileSync(join(repo, "lean-toolchain"), "utf8").trim() },
      compilerOptions: JSON.parse(stableText(repo, JSON.stringify(project.compilerOptions))),
      expected: queries.map(q => q.id), attempted: observations.map(o => o.id),
      resolved: observations.filter(o => o.status !== "refused").map(o => o.id),
      mismatching: observations.filter(o => o.status === "mismatch").map(o => o.id),
      refused: observations.filter(o => o.status === "refused").map(o => o.id),
      globalDiagnostics: globals.map(diagnostic), observations, sourceHashes,
      limitations: [`Compiler: ${COMPILER} ${version} (tsgo, decisions row 57), under ts/eff/tsconfig.json.`,
        "Finite TypeScript assignments under explicit target bindings: program E is an upper bound; every other column and primitive binding requires mutual assignability. No Lean semantic equivalence claim.",
        "Requirement carrier equality does not establish Lean service-key identity.",
        "Any/unknown inspection covers compared roots, generic payloads and local record fields; library implementation fields and class internals are opaque.",
        "Diagnostic line and column are counted over the file as a JavaScript string; every queried module is ASCII."],
      conforms: !globals.length && observations.every(o => o.status === "agree") }
  } finally { api.close() }
}

/** The object type of each subject that is an indexed access `X["m"]`, as the compiler parsed
 * it. Parsing only: no lib, no resolution, no checker. */
function receivers(repo: string, subjects: readonly string[]): (string | null)[] {
  const directory = join(repo, "ts/eff/__target_subjects__")
  const file = join(directory, "subjects.ts")
  const source = subjects.map((subject, index) => `type __S${index} = ${subject}`).join("\n") + "\n"
  const { api, project } = open(repo, directory, new Map([[file, source]]),
    { noLib: true, noResolve: true, types: [], noEmit: true })
  try {
    const sf = project.program.getSourceFile(file)
    if (!sf) throw new Error("target oracle: the compiler did not parse the subject module")
    const syntactic = project.program.getSyntacticDiagnostics(file)
    if (syntactic.length) throw new Error(`target oracle: a selected subject does not parse: ${syntactic.map(d => d.text).join("; ")}`)
    const { aliases } = names(sf)
    return subjects.map((_, index) => {
      const alias = aliases.get(`__S${index}`)
      if (!alias || !isTypeAliasDeclaration(alias) || !isIndexedAccessTypeNode(alias.type)) return null
      return project.emitter.printNode(alias.type.objectType)
    })
  } finally { api.close() }
}

const [, , requestPath, responsePath] = process.argv
if (!requestPath || !responsePath) throw new Error("checker.ts <request.json> <response.json>")
const request = JSON.parse(readFileSync(requestPath, "utf8")) as Record<string, unknown>
const repo = resolve(String(request.repo ?? ""))
if (!isAbsolute(repo) || !existsSync(join(repo, "ts/eff/tsconfig.json"))) throw new Error(`target oracle: ${repo} is not a checkout of this repository`)
const answer = request.kind === "subjects"
  ? { receivers: receivers(repo, request.subjects as string[]) }
  : report(repo, String(request.profile), request.queries as Query[])
writeFileSync(responsePath, JSON.stringify(answer))
