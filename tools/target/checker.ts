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
import { existsSync, readFileSync, realpathSync, writeFileSync } from "node:fs"
import { dirname, isAbsolute, join, relative, resolve } from "node:path"
import {
  API, NodeBuilderFlags, type Project, SignatureKind, SymbolFlags, type Type, TypeFlags,
} from "../../ts/eff/node_modules/@typescript/native-preview/dist/api/sync/api.js"
import type { Diagnostic as CompilerDiagnostic } from "../../ts/eff/node_modules/@typescript/native-preview/dist/api/sync/types.js"
import type { CallExpression, Node, SourceFile } from "../../ts/eff/node_modules/@typescript/native-preview/dist/ast/index.js"
import {
  isArrowFunction, isCallExpression, isExportDeclaration, isFunctionDeclaration, isFunctionTypeNode, isIdentifier, isIndexedAccessTypeNode,
  isNamedExports, isParameterDeclaration, isPropertyAccessExpression, isStringLiteral, isTypeAliasDeclaration, isTypeReferenceNode,
  isUnionTypeNode, isVariableDeclaration, isVariableStatement, SyntaxKind,
} from "../../ts/eff/node_modules/@typescript/native-preview/dist/ast/index.js"
import {
  bindingName, pairBindingName, pairImports, pairSource, querySource,
  type Axis, type Column, type Diagnostic, type Direction, type Issue, type Observation,
  type Pair, type PairObservation, type PairReport, type Query, type Report,
  type TruthWideningEntry, type TruthWideningRequest, type TruthWideningReport,
  type P2bRequest, type P2bReport, type P2bDiagnostic,
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

/** The values a module declares at its top level. The compiler's node lists subclass `Array`
 * with a constructor of their own, so they are copied before `flatMap` builds a new list. */
const topLevelValues = (file: SourceFile) => new Set([...file.statements].flatMap(statement =>
  isVariableStatement(statement) ? [...statement.declarationList.declarations].flatMap(d => isIdentifier(d.name) ? [d.name.text] : []) :
  isFunctionDeclaration(statement) && statement.name ? [statement.name.text] : []))

/** The file that declares a printed head, read from the sources instead of kept beside them. A
 * namespaced head (`Fiber.join`) is declared by the pinned `effect` module of its namespace.
 * Any other head is the prelude's, found through the prelude's own exports: the module a named
 * re-export takes it from, else the prelude itself, else the one `export *` module that declares
 * it. A helper that moves between the prelude's sibling files (`846ed8c0` moved `fold`,
 * `optionCase` and `caseTag` to `control.ts`) moves here with the prelude's export line. */
function bindingOwner(repo: string, project: Project, prelude: string, head: string): string {
  const dot = head.indexOf(".")
  if (dot >= 0) return join(repo, "ts/eff/node_modules/effect/dist", head.slice(0, dot) + ".d.ts")
  const source = (path: string) => {
    const file = project.program.getSourceFile(path)
    if (!file) throw new Error(`P2b: the compiler did not open ${localPath(repo, path)}`)
    return file
  }
  const wildcards: string[] = []
  for (const statement of source(prelude).statements) {
    if (!isExportDeclaration(statement) || statement.isTypeOnly || !statement.moduleSpecifier ||
      !isStringLiteral(statement.moduleSpecifier)) continue
    const target = resolve(dirname(prelude), statement.moduleSpecifier.text)
    if (!statement.exportClause) wildcards.push(target)
    else if (isNamedExports(statement.exportClause) &&
      statement.exportClause.elements.some(e => !e.isTypeOnly && e.name.text === head)) return target
  }
  if (topLevelValues(source(prelude)).has(head)) return prelude
  const declaring = wildcards.filter(path => topLevelValues(source(path)).has(head))
  if (declaring.length !== 1) throw new Error(`P2b: the prelude's exports name no single owner of ${head}`)
  return declaring[0]!
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
const inspections = new WeakMap<Project, Map<string, string[]>>()
function forbiddenTypes(project: Project, root: Type, allowUnknown: boolean): string[] {
  let inspected = inspections.get(project)
  if (!inspected) { inspected = new Map(); inspections.set(project, inspected) }
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
  try { return reportProject(repo, profile, queries, version, project, files, sources, fileOf) }
  finally { api.close() }
}

/** Reuse one project's inferred columns and assignment statements for a complete batch. */
function reportProject(repo: string, profile: string, queries: readonly Query[], version: string,
  project: Project, files: ReadonlyMap<string, string>, sources: ReadonlyMap<string, string>,
  fileOf: ReadonlyMap<string, string>): Report {
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
    // The pinned API batches this array into one getTypeAtLocations request.
    // Keep these AST objects in this Project; no node or type crosses a snapshot.
    const bindings = new Map(queries.map(q => {
      const sf = program.getSourceFile(fileOf.get(q.id)!)
      return [q.id, { sf, ...(sf ? names(sf) : { variables: new Map<string, Node>(), aliases: new Map<string, Node>() }) }] as const
    }))
    const typeNodes = [...bindings.values()].flatMap(binding => [
      ...axes.flatMap(axis => [binding.variables.get(`__${axis}_actual`), binding.variables.get(`__${axis}_expected`)]),
      binding.aliases.get("__Subject"),
    ]).filter((node): node is Node => node !== undefined)
    const measuredTypes = checker.getTypeAtLocation(typeNodes)
    const typesAt = new Map(typeNodes.map((node, index) => [node, measuredTypes[index]] as const))
    const observations: Observation[] = queries.map(q => {
      const file = fileOf.get(q.id)!
      const { sf, variables, aliases } = bindings.get(q.id)!
      const issues: Issue[] = [...q.inputIssues ?? []]
      if (!existsSync(resolve(repo, q.source))) issues.push({ code: "missing-source", message: q.source })
      if (!sf) issues.push({ code: "missing-query-source", message: q.id })
      if (globals.length) issues.push({ code: "dependency-diagnostic", message: "Compiler diagnostics in imported inputs; see globalDiagnostics" })
      const own = inSource.filter(d => resolve(d.fileName!) === resolve(repo, q.source))
      if (own.length) issues.push({ code: "source-diagnostic", message: `${own.length} compiler diagnostic(s) (${[...new Set(own.map(d => `TS${d.code}`))].join(", ")}) in ${localPath(repo, resolve(repo, q.source))}: ${stableText(repo, message(own[0]!))}` })
      const columns: Observation["columns"] = {}
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
        if (!actual) {
          if (q.expected[axis] !== undefined) issues.push({ code: "missing-type-metadata", axis, message: `Missing actual ${axis} binding` })
          continue
        }
        const expected = variables.get(`__${axis}_expected`)
        const actualType = typesAt.get(actual)
        const column: Column = { actual: actualType ? textOf(actualType, actual) : null, expected: q.expected[axis] ?? null,
          actualToExpected: null, expectedToActual: null, agreement: null }
        columns[axis] = column
        if (!expected) issues.push({ code: "missing-type-metadata", axis, message: `Missing expected ${axis}` })
        const expectedType = expected ? typesAt.get(expected) : undefined
        if (!actualType) issues.push({ code: "missing-type-metadata", axis, message: `Compiler returned no actual ${axis} type` })
        if (expected && !expectedType) issues.push({ code: "missing-type-metadata", axis, message: `Compiler returned no expected ${axis} type` })
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
      if (q.kind === "function" || q.kind === "callable") {
        const subject = aliases.get("__Subject")
        const type = subject && typesAt.get(subject)
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
        "Requirement assignments test the emitted full-key identifiers; they do not establish globally fresh identities across independently linked modules.",
        "Any/unknown inspection covers compared roots, generic payloads and local record fields; library implementation fields and class internals are opaque.",
        "Diagnostic line and column are counted over the file as a JavaScript string; every queried module is ASCII."],
      conforms: !globals.length && observations.every(o => o.status === "agree") }
}

/** The assignability differential (plan 1.10): one module per pair, both readings of both
 * directions. The axis guard does not run here — a bare pair is not an Effect column, and
 * `unknown` is a type of the algebra (decisions row 46), not contamination. */
function assignability(repo: string, questions: readonly Pair[]): PairReport {
  const directory = join(repo, "ts/eff/__assignability__")
  const sources = new Map<string, string>(), fileOf = new Map<string, string>()
  questions.forEach((p, index) => {
    const file = join(directory, `p${index}.ts`)
    sources.set(file, pairSource(p)); fileOf.set(p.id, file)
  })
  const version = compilerVersion(repo)
  const { api, project, files } = open(repo, directory, sources,
    { noEmit: true, typeRoots: [join(repo, "ts/eff/node_modules/@types")] })
  try {
    const { program, checker } = project
    const textOfFile = (file: string) => files.get(file) ?? (existsSync(file) ? readFileSync(file, "utf8") : "")
    const outside = [...program.getConfigFileParsingDiagnostics(), ...program.getProgramDiagnostics(),
      ...program.getGlobalDiagnostics()].filter(d => !d.fileName || !sources.has(d.fileName))
    if (outside.length) throw new Error(`target oracle: the assignability project does not compile: ${outside.map(d => d.text).join("; ")}`)
    const observations = questions.map((p): PairObservation => {
      const file = fileOf.get(p.id)!
      const sf = program.getSourceFile(file)
      const { variables, aliases } = sf ? names(sf) : { variables: new Map<string, Node>(), aliases: new Map<string, Node>() }
      const issues: Issue[] = []
      const ds = [...program.getSyntacticDiagnostics(file), ...program.getSemanticDiagnostics(file)]
      const onAssignment = (d: CompilerDiagnostic, direction: "leftToRight" | "rightToLeft") => {
        const id = variables.get(pairBindingName(direction))
        return id !== undefined && d.pos >= id.parent.getStart() && d.pos < id.parent.end
      }
      const other = ds.filter(d => !assignmentDiagnostics.has(d.code) ||
        !(["leftToRight", "rightToLeft"] as const).some(direction => onAssignment(d, direction)))
      if (!sf) issues.push({ code: "missing-pair-source", message: p.id })
      if (other.length) issues.push({ code: "pair-diagnostic", message: `${[...new Set(other.map(d => `TS${d.code}`))].join(", ")}: ${other[0]!.text}` })
      const leftNode = aliases.get("__Left"), rightNode = aliases.get("__Right")
      const left = leftNode && checker.getTypeAtLocation(leftNode)
      const right = rightNode && checker.getTypeAtLocation(rightNode)
      const clean = !issues.length && left !== undefined && right !== undefined
      const direction = (from: Type | undefined, to: Type | undefined, which: "leftToRight" | "rightToLeft"): Direction => ({
        assignable: clean && from && to ? checker.isTypeAssignableTo(from, to) : null,
        statement: clean ? !ds.some(d => onAssignment(d, which)) : null,
      })
      return { id: p.id, left: p.left, right: p.right,
        leftText: left ? checker.typeToString(left, leftNode, formatFlags) : null,
        rightText: right ? checker.typeToString(right, rightNode, formatFlags) : null,
        leftToRight: direction(left, right, "leftToRight"),
        rightToLeft: direction(right, left, "rightToLeft"),
        issues, diagnostics: ds.map(d => ({ code: d.code, file: d.fileName ? localPath(repo, d.fileName) : "<compiler>",
          line: d.fileName ? lineAndColumn(textOfFile(d.fileName), d.pos).line : 0,
          column: d.fileName ? lineAndColumn(textOfFile(d.fileName), d.pos).column : 0,
          message: stableText(repo, d.text) })) }
    })
    return { format: "effect4-assignability-report-v1",
      versions: { compiler: COMPILER, typescript: version,
        effect: (JSON.parse(readFileSync(join(repo, "ts/eff/node_modules/effect/package.json"), "utf8")) as { version: string }).version,
        lean: readFileSync(join(repo, "lean-toolchain"), "utf8").trim() },
      compilerOptions: JSON.parse(stableText(repo, JSON.stringify(project.compilerOptions))),
      observations,
      limitations: [`Compiler: ${COMPILER} ${version} (tsgo, decisions row 57), under ts/eff/tsconfig.json.`,
        "Two readings per direction: the checker's own relation (isTypeAssignableTo) and one ordinary assignment statement. They are reported side by side; a row where they differ is a finding, not a verdict.",
        "A finite set of pairs over a small alphabet per head. No claim about types outside it, and no claim that the target's order and `Ty.sub` agree beyond these rows.",
        "The any/unknown guard of the program lane does not run: `unknown` is the top of this algebra (decisions row 46) and is a compared type here."] }
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

/** The truth fixture consumer, with one API client and two snapshots for the complete batch.
 * The first snapshot checks both module views and bidirectional inferred A/E/R assignments.
 * Its compiler AST selects the exact union node. Only that node's source span changes.
 * The second snapshot requires TS2345 at the request or TS2322 in the callback. */
function truthWidenings(repo: string, request: TruthWideningRequest): TruthWideningReport {
  const version = compilerVersion(repo)
  if (version !== "7.0.0-dev.20260629.1") throw new Error(`truth widening: unsupported tsgo pin ${version}`)
  const work = resolve(request.work)
  const directory = join(work, "__widening_queries__")
  const sources = new Map<string, string>()
  const specs = [
    { name: "pJoinedFirstNumber", space: "L", method: "first", join: 0, argument: 0, diagnostic: 2345 },
    { name: "pJoinedFirstString", space: "L", method: "first", join: 0, argument: 0, diagnostic: 2345 },
    { name: "pJoinedModifyNumber", space: "Ref", method: "modify", join: 1, argument: 1, diagnostic: 2322 },
    { name: "pJoinedModifyString", space: "Ref", method: "modify", join: 1, argument: 1, diagnostic: 2322 },
  ] as const
  const fileOf = new Map<string, { positive: string; inferred: string; query: string }>()
  const entryOf = new Map<string, TruthWideningEntry>()
  for (const spec of specs) {
    const entries = request.manifest.programs.filter(entry => entry.name === spec.name)
    const entry = entries[0]
    if (entries.length !== 1 || !entry?.wellTyped || !entry.type || entry.expr === null ||
      entry.decl === null || entry.declInferred === null) throw new Error(`truth widening: ${spec.name} is missing, refused, or duplicated`)
    if (!entry.type.requiresEmpty || entry.type.requires.length !== 0) throw new Error(`truth widening: ${spec.name} has a nonempty requirement row`)
    const source = readFileSync(join(work, "generated", `${spec.name}.ts`), "utf8")
    if (!source.endsWith(entry.decl)) throw new Error(`truth widening: ${spec.name} executed bytes differ from its declaration`)
    const positive = join(directory, `${spec.name}.positive.ts`)
    const inferred = join(directory, `${spec.name}.inferred.ts`)
    const query = join(directory, `${spec.name}.query.ts`)
    sources.set(positive, source)
    // Preserve the exact executed import header; replace only the manifest's declaration view.
    sources.set(inferred, source.slice(0, source.length - entry.decl.length) + entry.declInferred)
    sources.set(query, querySource({
      id: spec.name, source: inferred,
      imports: ['import type { Option, Ref } from "effect"', `import type * as Program from ${JSON.stringify(inferred)}`],
      subject: "typeof Program.main", kind: "program",
      expected: { A: entry.type.answer, E: entry.type.error, R: "never" },
    }))
    fileOf.set(spec.name, { positive, inferred, query }); entryOf.set(spec.name, entry)
  }
  const mutantOf = new Map<string, string>()
  for (const spec of [specs[0], specs[2]]) {
    const mutant = join(directory, `${spec.name}.missing-member.ts`)
    sources.set(mutant, sources.get(fileOf.get(spec.name)!.positive)!)
    mutantOf.set(spec.name, mutant)
  }
  const corruptedFile = join(directory, "pJoinedModifyNumber.wrong-update.ts")
  sources.set(corruptedFile, sources.get(fileOf.get("pJoinedModifyNumber")!.positive)!)
  const options = JSON.parse(readFileSync(join(work, "tsconfig.json"), "utf8")).compilerOptions as Record<string, unknown>
  const { api, project, files } = open(repo, directory, sources, options)
  const diagnostics = (p: Project) => [...p.program.getConfigFileParsingDiagnostics(),
    ...p.program.getProgramDiagnostics(), ...p.program.getGlobalDiagnostics(),
    ...p.program.getSyntacticDiagnostics(), ...p.program.getSemanticDiagnostics()]
  const message = (d: CompilerDiagnostic): string => [d.text, ...(d.messageChain ?? []).map(message)].join(" ")
  const diagnostic = (d: CompilerDiagnostic): P2bDiagnostic => {
    const text = d.fileName ? files.get(d.fileName) ?? readFileSync(d.fileName, "utf8") : ""
    const position = lineAndColumn(text, d.pos)
    return { code: d.code, file: d.fileName ? localPath(repo, d.fileName) : "<compiler>",
      line: position.line, column: position.column, message: stableText(repo, message(d)),
      start: d.pos, end: d.end, compiler: d }
  }
  const sourceHashes: Record<string, string> = {}
  const positives: TruthWideningReport["positives"] = []
  try {
    const green = diagnostics(project)
    if (green.length) throw new Error(`truth widening: positive or inferred query diagnostics: ${JSON.stringify(green.map(diagnostic))}`)
    // Query types are compiler data. Assignment statements, not typeToString spellings, decide agreement.
    for (const spec of specs) {
      const entry = entryOf.get(spec.name)!
      const paths = fileOf.get(spec.name)!
      for (const file of [paths.positive, paths.inferred]) {
        const sf = project.program.getSourceFile(file)
        if (!sf) throw new Error(`truth widening: missing parsed module ${file}`)
        const main = names(sf).variables.get("main")
        if (!main || !isVariableDeclaration(main.parent) || !main.parent.initializer ||
          main.parent.initializer.getText(sf) !== entry.expr) throw new Error(`truth widening: ${spec.name} lost its actual printed initializer`)
      }
      const sf = project.program.getSourceFile(paths.query)
      if (!sf) throw new Error(`truth widening: missing inferred query ${spec.name}`)
      const variables = names(sf).variables
      const columns: Partial<Record<Axis, Column>> = {}
      const nodes = ["A", "E", "R"].flatMap(axis => [variables.get(`__${axis}_actual`), variables.get(`__${axis}_expected`)])
      if (nodes.some(node => !node)) throw new Error(`truth widening: incomplete inferred query ${spec.name}`)
      const types = project.checker.getTypeAtLocation(nodes as Node[])
      for (const [i, axis] of (["A", "E", "R"] as const).entries()) {
        const actual = types[i * 2], expected = types[i * 2 + 1]
        if (!actual || !expected || forbiddenTypes(project, actual, false).length || forbiddenTypes(project, expected, false).length) {
          throw new Error(`truth widening: unresolved inferred ${spec.name}/${axis}`)
        }
        const actualToExpected = project.checker.isTypeAssignableTo(actual, expected)
        const expectedToActual = project.checker.isTypeAssignableTo(expected, actual)
        if (!actualToExpected || !expectedToActual) throw new Error(`truth widening: inferred ${spec.name}/${axis} differs`)
        columns[axis] = { actual: project.checker.typeToString(actual, nodes[i * 2]!, formatFlags),
          expected: axis === "R" ? "never" : axis === "A" ? entry.type!.answer : entry.type!.error,
          actualToExpected, expectedToActual, agreement: "exact" }
      }
      positives.push({ fixture: spec.name, columns })
    }
    // Read the selected functions' actual uninstantiated signatures, including the data-first
    // Ref overload. Type parameter identities connect request/cell/reply positions.
    const genericBindings: TruthWideningReport["genericBindings"] = []
    const typeArguments = (type: Type | undefined): readonly Type[] =>
      type?.isTypeReference() ? project.checker.getTypeArguments(type) : []
    for (const spec of [specs[0], specs[2]]) {
      const sf = project.program.getSourceFile(fileOf.get(spec.name)!.positive)!
      const calls: CallExpression[] = []
      const walk = (node: Node) => {
        if (isCallExpression(node) && isPropertyAccessExpression(node.expression) &&
          isIdentifier(node.expression.expression) && node.expression.expression.text === spec.space &&
          node.expression.name.text === spec.method) calls.push(node)
        node.forEachChild(walk)
      }
      sf.forEachChild(walk)
      if (calls.length !== 1) throw new Error(`truth widening: ${spec.name} binding call inventory differs`)
      const type = project.checker.getTypeAtLocation(calls[0]!.expression)
      if (!type) throw new Error(`truth widening: ${spec.name} binding is unresolved`)
      const actualCall = calls[0]!
      const selected = project.checker.getResolvedSignature(actualCall)
      const selectedDeclaration = selected?.declaration?.resolve(project)
      if (!selectedDeclaration) throw new Error(`truth widening: ${spec.name} actual call has no resolved declaration`)
      const selectedFile = selectedDeclaration.getSourceFile()
      const signatures = project.checker.getSignaturesOfType(type, SignatureKind.Call)
        .filter(signature => {
          const declaration = signature.declaration?.resolve(project)
          return signature.getParameters().length === spec.argument + 1 && declaration &&
            declaration.getSourceFile().fileName === selectedFile.fileName &&
            declaration.getStart() === selectedDeclaration.getStart() && declaration.end === selectedDeclaration.end
        })
      if (signatures.length !== 1) throw new Error(`truth widening: ${spec.name} actual overload inventory differs`)
      const signature = signatures[0]!
      const parameters = signature.getTypeParameters()
      const declaration = signature.declaration?.resolve(project)
      if (!declaration || !(isArrowFunction(declaration) || isFunctionTypeNode(declaration)) ||
        declaration.typeParameters?.length !== spec.join + 1 || parameters.length !== spec.join + 1) {
        throw new Error(`truth widening: ${spec.name} actual generic declaration differs`)
      }
      const parameterNames = Array.from(declaration.typeParameters, parameter => parameter.name.text)
      if (parameterNames.join(",") !== (spec.join === 0 ? "A" : "A,B")) {
        throw new Error(`truth widening: ${spec.name} generic parameter order differs`)
      }
      const firstArgument = project.checker.getParameterType(signature, 0)
      if (typeArguments(firstArgument)[0]?.id !== parameters[0]!.id) {
        throw new Error(`truth widening: ${spec.name} request/cell does not use the first generic parameter`)
      }
      const result = project.checker.getReturnTypeOfSignature(signature)
      const resultArguments = typeArguments(result)
      if (resultArguments[1]?.flags !== TypeFlags.Never || resultArguments[2]?.flags !== TypeFlags.Never) {
        throw new Error(`truth widening: ${spec.name} binding error/requirement columns differ`)
      }
      if (spec.join === 0) {
        const payload = resultArguments[0]
        if (!payload?.isUnionType() || !payload.getTypes().every(member =>
          typeArguments(member)[0]?.id === parameters[0]!.id)) {
          throw new Error("truth widening: L.first reply does not retain its request element parameter")
        }
      } else {
        const callback = project.checker.getParameterType(signature, 1)
        const callbacks = callback ? project.checker.getSignaturesOfType(callback, SignatureKind.Call) : []
        const callbackSignature = callbacks[0]
        const pair = callbackSignature && project.checker.getReturnTypeOfSignature(callbackSignature)
        const pairArguments = typeArguments(pair)
        if (callbacks.length !== 1 || !callbackSignature || callbackSignature.getParameters().length !== 1 ||
          project.checker.getParameterType(callbackSignature, 0)?.id !== parameters[0]!.id ||
          !pair || !project.checker.isTupleType(pair) || pairArguments.length !== 2 ||
          pairArguments[0]?.id !== parameters[1]!.id || pairArguments[1]?.id !== parameters[0]!.id ||
          resultArguments[0]?.id !== parameters[1]!.id) {
          throw new Error("truth widening: Ref.modify does not connect <cell, reply> to [reply, nextCell]")
        }
      }
      const declarationFile = declaration.getSourceFile()
      genericBindings.push({ binding: `${spec.space}.${spec.method}`, typeParameters: parameterNames,
        selectedCall: { file: localPath(repo, sf.fileName), start: actualCall.getStart(sf), end: actualCall.end },
        selectedDeclaration: { file: localPath(repo, selectedFile.fileName), start: selectedDeclaration.getStart(selectedFile), end: selectedDeclaration.end },
        declaration: { file: localPath(repo, declarationFile.fileName),
          ...lineAndColumn(declarationFile.text, declaration.getStart(declarationFile)) },
        signature: project.emitter.printNode(declaration) })
    }
    const bounds = new Map<string, { start: number; end: number }>()
    const changedSpans = new Map<string, { start: number; end: number; replacement: string }>()
    for (const spec of [specs[0], specs[2]]) {
      const file = mutantOf.get(spec.name)!
      const sf = project.program.getSourceFile(file)
      if (!sf) throw new Error(`truth widening: missing parsed mutant ${spec.name}`)
      const calls: CallExpression[] = []
      const walk = (node: Node) => {
        if (isCallExpression(node) && isPropertyAccessExpression(node.expression) &&
          isIdentifier(node.expression.expression) && node.expression.expression.text === spec.space &&
          node.expression.name.text === spec.method) calls.push(node)
        node.forEachChild(walk)
      }
      sf.forEachChild(walk)
      const call = calls[0]
      if (calls.length !== 1 || !call || call.typeArguments?.length !== spec.join + 1) throw new Error(`truth widening: ${spec.name} typed call inventory differs`)
      const typeArguments = call.typeArguments!
      const union = typeArguments[spec.join]
      if (!union || !isUnionTypeNode(union) || union.types.length !== 2 ||
        !union.types.some(t => t.kind === SyntaxKind.NumberKeyword) ||
        !union.types.some(t => t.kind === SyntaxKind.StringKeyword)) throw new Error(`truth widening: ${spec.name} does not carry number | string`)
      if (spec.join === 1 && typeArguments[0]?.kind !== SyntaxKind.NumberKeyword) throw new Error(`truth widening: ${spec.name} changes the cell type`)
      const number = union.types.find(t => t.kind === SyntaxKind.NumberKeyword)!
      const start = union.getStart(sf), end = union.end
      const replacement = number.getText(sf)
      const changed = sf.text.slice(0, start) + replacement + sf.text.slice(end)
      const argument = call.arguments[spec.argument]
      if (!argument || argument.getStart(sf) < end) throw new Error(`truth widening: ${spec.name} has no affected argument`)
      const shift = replacement.length - (end - start)
      bounds.set(file, { start: argument.getStart(sf) + shift, end: argument.end + shift })
      changedSpans.set(file, { start, end, replacement })
      files.set(file, changed)
    }
    // Corrupt only the two next-state expressions inside the same actual printed callback.
    const corruptedSf = project.program.getSourceFile(corruptedFile)
    if (!corruptedSf) throw new Error("truth widening: missing parsed update control")
    const modifyCalls: CallExpression[] = []
    const findModify = (node: Node) => {
      if (isCallExpression(node) && isPropertyAccessExpression(node.expression) &&
        isIdentifier(node.expression.expression) && node.expression.expression.text === "Ref" &&
        node.expression.name.text === "modify") modifyCalls.push(node)
      node.forEachChild(findModify)
    }
    corruptedSf.forEachChild(findModify)
    const callback = modifyCalls[0]?.arguments[1]
    if (modifyCalls.length !== 1 || !callback || !isArrowFunction(callback) ||
      callback.parameters.length !== 1 || !isIdentifier(callback.parameters[0]!.name)) {
      throw new Error("truth widening: unexpected actual modify callback for update control")
    }
    const parameter = callback.parameters[0]!.name.text
    const increments: CallExpression[] = []
    const findIncrement = (node: Node) => {
      if (isCallExpression(node) && isIdentifier(node.expression) && node.expression.text === "succ" &&
        node.arguments.length === 1 && isIdentifier(node.arguments[0]!) &&
        node.arguments[0]!.text === parameter) increments.push(node)
      node.forEachChild(findIncrement)
    }
    findIncrement(callback.body)
    if (increments.length !== 2) throw new Error("truth widening: next-state expression inventory differs")
    let corruptedSource = corruptedSf.text
    for (const increment of increments.sort((a, b) => b.getStart(corruptedSf) - a.getStart(corruptedSf))) {
      corruptedSource = corruptedSource.slice(0, increment.getStart(corruptedSf)) +
        increment.arguments[0]!.getText(corruptedSf) + corruptedSource.slice(increment.end)
    }
    files.set(corruptedFile, corruptedSource)
    const snapshot = api.updateSnapshot({ openProjects: [join(directory, "tsconfig.json")],
      fileChanges: { changed: [...mutantOf.values(), corruptedFile] } })
    const redProject = snapshot.getProjects()[0]
    if (!redProject) throw new Error("truth widening: the mutant snapshot opened no project")
    const red = diagnostics(redProject)
    if (red.length !== mutantOf.size) throw new Error(`truth widening: unexpected mutant/dependency diagnostics: ${JSON.stringify(red.map(diagnostic))}`)
    const mutants: TruthWideningReport["mutants"] = []
    for (const [fixture, file] of mutantOf) {
      const span = bounds.get(file)!
      const own = red.filter(d => d.fileName === file)
      if (own.length !== 1 || own[0]!.code !== specs.find(spec => spec.name === fixture)!.diagnostic || own[0]!.pos < span.start || own[0]!.pos >= span.end) {
        throw new Error(`truth widening: ${fixture} needs its exact intended diagnostic at the changed call argument: ${JSON.stringify(own.map(diagnostic))}`)
      }
      mutants.push({ fixture, removedMember: "string", sourceHash: hash(files.get(file)!), source: files.get(file)!,
        changedSpan: changedSpans.get(file)!, intendedSpan: span, diagnostics: own.map(diagnostic) })
    }
    for (const file of redProject.program.getSourceFileNames()) {
      sourceHashes[localPath(repo, file)] = hash(files.get(file) ?? readFileSync(file, "utf8"))
    }
    return { format: "effect4-truth-widenings-v1", conforms: true,
      versions: { compiler: COMPILER, typescript: version,
        effect: JSON.parse(readFileSync(join(repo, "ts/eff/node_modules/effect/package.json"), "utf8")).version },
      compilerOptions: project.compilerOptions, sourceHashes, positives, mutants, genericBindings,
      corruptedUpdates: [{ fixture: "pJoinedModifyNumber", source: corruptedSource,
        sourceHash: hash(corruptedSource), mutationCount: increments.length }],
      limitations: ["Finite compiler evidence for four printed fixtures and two call-argument mutations.",
        "No program execution or source-readback theorem follows from this compiler receipt."] }
  } finally { api.close() }
}

/** Finite P2b collection: actual typed expressions, one client, and two snapshots.
 * Exact inferred columns stay separate from module compilation. A single-member companion
 * remains visible when the existing host type differs from the source projection. */
function p2bTarget(repo: string, request: P2bRequest): P2bReport {
  const version = compilerVersion(repo)
  if (version !== "7.0.0-dev.20260629.1") throw new Error(`P2b: unsupported tsgo pin ${version}`)
  const work = resolve(request.work), module = resolve(request.module)
  const directory = join(work, "__p2b__")
  if (module !== join(directory, "printed.ts")) throw new Error("P2b: module must sit beside its query project")
  const manifest = request.manifest
  if (manifest.format !== "effect4-p2b-target-v1") throw new Error("P2b: wrong fixture format")
  const families = {
    options: ["option"], "list-fold": ["foldInferred", "foldStored"],
    fibers: ["fiberJoin", "fiberAwait", "fiberInterrupt", "fiberRunIn", "fiberInterruptAll",
      "fiberInterruptAllAs", "fiberAwaitAllFirst", "forkChild", "forkDetach", "forkScoped", "forkIn"],
    "exit-scope": ["scopeClose", "scoped", "acquireRelease"],
    cause: ["causeIsFail", "causeIsDie", "causeIsInterrupt", "causeError"],
    "tag-record": ["tag", "recordTag", "recordRequired", "recordOptional", "recordSet"],
  }
  const expectedNames = Object.values(families).flat().flatMap(name => [name + "Joined", name + "Single"])
  if (manifest.fixtures.length !== expectedNames.length ||
    expectedNames.some(name => manifest.fixtures.filter(f => f.name === name).length !== 1)) {
    throw new Error("P2b: approved fixture inventory is incomplete or duplicated")
  }
  for (const [family, names] of Object.entries(families)) for (const name of names) {
    for (const joined of [true, false]) {
      const fixture = manifest.fixtures.find(f => f.name === name + (joined ? "Joined" : "Single"))!
      if (fixture.family !== family || fixture.joined !== joined ||
        fixture.companion !== name + (joined ? "Single" : "Joined")) throw new Error(`P2b: wrong companion at ${fixture.name}`)
    }
  }
  const negativeSpecs = [
    { name: "rawFiberAwaitAllJoined", diagnostic: 4104, difference: "mutable Array versus checked ReadonlyArray" },
    { name: "rawFiberAwaitAllSingle", diagnostic: 4104, difference: "mutable Array versus checked ReadonlyArray" },
    { name: "recordSetLiteralSingle", diagnostic: 2322, difference: "literal true versus checked boolean" },
  ]
  if (manifest.negativeObservations.length !== negativeSpecs.length || negativeSpecs.some(spec =>
    manifest.negativeObservations.filter(f => f.name === spec.name && f.expectedDiagnostic === spec.diagnostic &&
      f.difference === spec.difference).length !== 1)) throw new Error("P2b: explicit negative observation inventory differs")
  const oldRefusals = { interruptScoped: "interruptScoped", awaitAllFailFast: "awaitAllFailFast",
    snapshotChildren: "snapshotChildren", awaitNewChildren: "awaitNewChildren",
    forkInChild: "forkIn:child", forkScopedChild: "forkScoped:child" }
  if (manifest.refusals.length !== Object.keys(oldRefusals).length ||
    Object.entries(oldRefusals).some(([name, reason]) => manifest.refusals.filter(f =>
      f.name === name && f.reason === reason && typeof f.checkerAdmits === "boolean").length !== 1)) {
    throw new Error("P2b: retained raw/typed refusal inventory differs")
  }
  const queryOf = (f: P2bRequest["manifest"]["fixtures"][number]): Query => ({ id: f.name, source: localPath(repo, module),
    imports: [...pairImports, 'import * as Printed from "./printed.ts"'], subject: `typeof Printed.${f.name}`, kind: "function",
    expected: { ...f.columns, request: f.request }, provenance: { family: f.family, companion: f.companion,
      joined: f.joined, printer: "Effect4.Program.printTyped", evidence: manifest.evidence } })
  const queries = manifest.fixtures.map(queryOf), negativeQueries = manifest.negativeObservations.map(queryOf)
  const sources = new Map<string, string>(), fileOf = new Map<string, string>()
  const allQueries = [...queries, ...negativeQueries]
  allQueries.forEach((q, index) => {
    const file = join(directory, `q${index}.ts`)
    sources.set(file, querySource(q)); fileOf.set(q.id, file)
  })
  // One affected union node per selected operation. Other type arguments and callback syntax stay intact.
  const specs: Array<{ name: string; head: string; index: number; argument: number; fiberPayload?: boolean; intendedCode?: number }> = [
    { name: "optionJoined", head: "optionCase", index: 0, argument: 0, intendedCode: 2379 },
    { name: "foldStoredJoined", head: "fold", index: 1, argument: 0 },
    { name: "foldInferredJoined", head: "fold", index: -1, argument: 0 },
    { name: "fiberJoinJoined", head: "Fiber.join", index: 0, argument: 0 },
    { name: "fiberAwaitAllFirstJoined", head: "Fiber.awaitAll", index: 0, argument: 0, fiberPayload: true },
    { name: "scopeCloseJoined", head: "Scope.close", index: 0, argument: 1, intendedCode: 2379 },
    ...["causeIsFail", "causeIsDie", "causeIsInterrupt", "causeError"].map(head =>
      ({ name: head + "Joined", head, index: 1, argument: 0 })),
    { name: "tagJoined", head: "caseTag", index: 0, argument: 0 },
    { name: "recordTagJoined", head: "caseTagR", index: 0, argument: 0 },
    ...["recordRequired", "recordOptional", "recordSet"].map(head =>
      ({ name: head + "Joined", head, index: 0, argument: 0 })),
  ]
  // Each clone contains the original imports and exactly one original declaration.
  // The module's own complete compilation still covers the entire collection.
  const moduleSource = readFileSync(module, "utf8")
  const firstDeclaration = manifest.fixtures[0]!.declaration
  const prefixLength = moduleSource.indexOf(firstDeclaration)
  if (prefixLength < 0 || moduleSource !== moduleSource.slice(0, prefixLength) +
    [...manifest.fixtures, ...manifest.negativeObservations].map(f => f.declaration).join("\n\n") + "\n") throw new Error("P2b: module does not contain the exact emitted declarations")
  const prefix = moduleSource.slice(0, prefixLength)
  const mutantOf = new Map(specs.map(spec => {
    const fixture = manifest.fixtures.find(f => f.name === spec.name)!
    const file = join(directory, spec.name + ".missing-member.ts")
    sources.set(file, prefix + fixture.declaration + "\n")
    return [spec.name, file] as const
  }))
  const options = JSON.parse(readFileSync(join(work, "tsconfig.json"), "utf8")).compilerOptions as Record<string, unknown>
  const { api, project, files } = open(repo, directory, sources, options)
  const diagnostics = (p: Project) => [...p.program.getConfigFileParsingDiagnostics(), ...p.program.getProgramDiagnostics(),
    ...p.program.getGlobalDiagnostics(), ...p.program.getSyntacticDiagnostics(), ...p.program.getSemanticDiagnostics()]
  const message = (d: CompilerDiagnostic): string => [d.text, ...(d.messageChain ?? []).map(message)].join(" ")
  const diagnostic = (d: CompilerDiagnostic): P2bDiagnostic => {
    const text = d.fileName ? files.get(d.fileName) ?? readFileSync(d.fileName, "utf8") : ""
    const position = lineAndColumn(text, d.pos)
    return { code: d.code, file: d.fileName ? localPath(repo, d.fileName) : "<compiler>",
      ...position, message: stableText(repo, message(d)), start: d.pos, end: d.end, compiler: d }
  }
  try {
    const sf = project.program.getSourceFile(module)
    if (!sf) throw new Error("P2b: actual emitted module was not opened")
    const variables = names(sf).variables
    for (const fixture of [...manifest.fixtures, ...manifest.negativeObservations]) {
      const name = variables.get(fixture.name)
      const declaration = name?.parent
      if (!declaration || !isVariableDeclaration(declaration) || !declaration.initializer ||
        declaration.type || !isArrowFunction(declaration.initializer) || declaration.initializer.type ||
        declaration.initializer.getText(sf) !== fixture.initializer ||
        declaration.initializer.body.getText(sf) !== fixture.body) throw new Error(`P2b: ${fixture.name} lost actual inferred typed syntax`)
    }
    const green = diagnostics(project)
    const queryFiles = new Set(fileOf.values()), mutantFiles = new Set(mutantOf.values())
    const moduleDiagnostics = green.filter(d => !d.fileName || (!queryFiles.has(d.fileName) && !mutantFiles.has(d.fileName))).map(diagnostic)
    const columns = reportProject(repo, "effect@4.0.0-rc.112/P2b-typed-fixtures", queries, version, project, files, sources, fileOf)
    const negativeColumns = reportProject(repo, "effect@4.0.0-rc.112/P2b-retained-negative-comparisons", negativeQueries,
      version, project, files, sources, fileOf)
    const negativeBindings = negativeQueries.map(q => {
      const file = fileOf.get(q.id)!, parsed = project.program.getSourceFile(file)
      if (!parsed) throw new Error(`P2b: negative query is absent ${q.id}`)
      return { q, file, parsed, variables: names(parsed).variables }
    })
    const negativeNodes = negativeBindings.flatMap(b => (["A", "E", "R", "request"] as const).flatMap(axis =>
      [b.variables.get(`__${axis}_actual`), b.variables.get(`__${axis}_expected`)]))
    if (negativeNodes.some(node => !node)) throw new Error("P2b: retained negative comparison lacks type metadata")
    const negativeTypes = project.checker.getTypeAtLocation(negativeNodes as Node[])
    const expectedNegatives: P2bReport["expectedNegatives"] = negativeBindings.map((binding, i) => {
      const fixture = manifest.negativeObservations.find(f => f.name === binding.q.id)!
      const reverse = binding.variables.get(bindingName("A", "expectedToActual"))?.parent
      if (!reverse) throw new Error(`P2b: missing retained reverse assignment ${fixture.name}`)
      const intendedSpan = { start: reverse.getStart(binding.parsed), end: reverse.end }
      const own = green.filter(d => d.fileName === binding.file)
      const relations: P2bReport["expectedNegatives"][number]["relations"] = {}
      let clean = true
      for (const [j, axis] of (["A", "E", "R", "request"] as const).entries()) {
        const actual = negativeTypes[i * 8 + j * 2], expected = negativeTypes[i * 8 + j * 2 + 1]
        if (!actual || !expected || forbiddenTypes(project, actual, false).length || forbiddenTypes(project, expected, false).length) {
          clean = false; continue
        }
        relations[axis] = { actualToExpected: project.checker.isTypeAssignableTo(actual, expected),
          expectedToActual: project.checker.isTypeAssignableTo(expected, actual) }
      }
      const observation = negativeColumns.observations.find(o => o.id === fixture.name)!
      const conforms = clean && observation.status === (fixture.expectedDiagnostic === 4104 ? "refused" : "mismatch") &&
        own.length === 1 && own[0]!.code === fixture.expectedDiagnostic &&
        own[0]!.pos >= intendedSpan.start && own[0]!.pos < intendedSpan.end &&
        relations.A?.actualToExpected === true && relations.A.expectedToActual === false &&
        (["E", "R", "request"] as const).every(axis => relations[axis]?.actualToExpected && relations[axis]?.expectedToActual)
      return { fixture: fixture.name, difference: fixture.difference, oracleStatus: observation.status,
        relations, intendedCode: fixture.expectedDiagnostic, intendedSpan, diagnostics: own.map(diagnostic), conforms }
    })
    const edits = new Map<string, { changedSpan: { start: number; end: number; replacement: string }; intendedSpan: { start: number; end: number }; resolvedDeclaration: { file: string; start: number; end: number } }>()
    for (const spec of specs) {
      const file = mutantOf.get(spec.name)!, parsed = project.program.getSourceFile(file)
      if (!parsed) throw new Error(`P2b: missing parsed clone ${spec.name}`)
      const calls: CallExpression[] = []
      const walk = (node: Node) => {
        if (isCallExpression(node)) {
          const direct = node.expression.getText(parsed) === spec.head
          const curried = ["recordRequired", "recordOptional", "recordSet"].includes(spec.head) &&
            isCallExpression(node.expression) && node.expression.expression.getText(parsed) === spec.head
          if ((direct || curried) && (spec.index < 0 || spec.fiberPayload || node.typeArguments?.[spec.index] && isUnionTypeNode(node.typeArguments[spec.index]!))) calls.push(node)
        }
        node.forEachChild(walk)
      }
      parsed.forEachChild(walk)
      const call = calls[0]
      if (calls.length !== 1 || !call) throw new Error(`P2b: ${spec.name} call inventory differs`)
      const callback = spec.index < 0 ? call.arguments[2] : undefined
      const argumentType = call.typeArguments?.[spec.index]
      if (spec.fiberPayload && (!argumentType || !isTypeReferenceNode(argumentType) ||
        argumentType.typeName.getText(parsed) !== "Fiber.Fiber" || argumentType.typeArguments?.length !== 2)) {
        throw new Error(`P2b: ${spec.name} does not carry its checked Fiber<A,E>`)
      }
      const union = spec.index < 0 && callback && isArrowFunction(callback) ? callback.parameters[1]?.type :
        spec.fiberPayload && argumentType && isTypeReferenceNode(argumentType) ? argumentType.typeArguments?.[0] : argumentType
      if (!union || !isUnionTypeNode(union) || union.types.length !== 2) throw new Error(`P2b: ${spec.name} has no exact two-member union`)
      const retained = union.types.find(t => t.kind === SyntaxKind.NumberKeyword) ?? union.types[0]!
      const start = union.getStart(parsed), end = union.end, replacement = retained.getText(parsed)
      const argument = call.arguments[spec.argument]
      if (!argument) throw new Error(`P2b: ${spec.name} has no affected argument`)
      const shifted = (position: number) => position >= end ? position + replacement.length - (end - start) : position
      const resolved = project.checker.getResolvedSignature(call)?.declaration?.resolve(project)
      if (!resolved) throw new Error(`P2b: ${spec.name} actual call has no selected declaration`)
      const declarationFile = resolved.getSourceFile()
      const owner = bindingOwner(repo, project, join(work, "prelude.ts"), spec.head)
      if (realpathSync(declarationFile.fileName) !== realpathSync(owner)) throw new Error(`P2b: ${spec.name} resolves outside its actual binding owner`)
      edits.set(file, { changedSpan: { start, end, replacement },
        intendedSpan: { start: shifted(argument.getStart(parsed)), end: shifted(argument.end) },
        resolvedDeclaration: { file: localPath(repo, declarationFile.fileName), start: resolved.getStart(declarationFile), end: resolved.end } })
      files.set(file, parsed.text.slice(0, start) + replacement + parsed.text.slice(end))
    }
    const redProject = api.updateSnapshot({ openProjects: [join(directory, "tsconfig.json")],
      fileChanges: { changed: [...mutantOf.values()] } }).getProjects()[0]
    if (!redProject) throw new Error("P2b: mutant snapshot opened no project")
    const red = diagnostics(redProject)
    const mutants = specs.map(spec => {
      const file = mutantOf.get(spec.name)!, edit = edits.get(file)!
      const baseline = green.filter(d => d.fileName === file), own = red.filter(d => d.fileName === file)
      const intendedCode = spec.intendedCode ?? 2345
      const conforms = baseline.length === 0 && own.length === 1 && own[0]!.code === intendedCode &&
        own[0]!.pos >= edit.intendedSpan.start && own[0]!.pos < edit.intendedSpan.end
      return { fixture: spec.name, companion: manifest.fixtures.find(f => f.name === spec.name)!.companion,
        source: files.get(file)!, sourceHash: hash(files.get(file)!), ...edit, intendedCode,
        baselineDiagnostics: baseline.map(diagnostic), diagnostics: own.map(diagnostic), conforms }
    })
    const sourceHashes: Record<string, string> = { ...columns.sourceHashes, "P2b.manifest": hash(JSON.stringify(manifest)), "P2b.printed-module": hash(moduleSource) }
    for (const [name, file] of mutantOf) sourceHashes["P2b.mutant." + name] = hash(files.get(file)!)
    const pairs = manifest.fixtures.filter(f => f.joined).map(f => ({ joined: f.name, single: f.companion,
      joinedStatus: columns.observations.find(o => o.id === f.name)!.status,
      singleStatus: columns.observations.find(o => o.id === f.companion)!.status }))
    const moduleCompiles = moduleDiagnostics.length === 0, exactColumnsAgree = columns.conforms
    // A correct intended diagnostic cannot hide a new diagnostic outside the changed clone.
    const outsideIdentity = (ds: readonly CompilerDiagnostic[]) => ds.filter(d => !d.fileName || !mutantFiles.has(d.fileName))
      .map(d => JSON.stringify(d)).sort().join("\n")
    const mutantsConform = mutants.every(m => m.conforms) && outsideIdentity(green) === outsideIdentity(red)
    const expectedNegativesConform = expectedNegatives.every(n => n.conforms) && negativeColumns.conforms === false
    return { format: "effect4-p2b-target-report-v1", conforms: moduleCompiles && exactColumnsAgree && expectedNegativesConform && mutantsConform,
      moduleCompiles, exactColumnsAgree, mutantsConform, expectedNegativesConform,
      scope: { exactSuccesses: queries.map(q => q.id), expectedNegativeComparisons: negativeQueries.map(q => q.id),
        observation: "awaitAll success observes the first Exit through get; recordSet success supplies a Boolean parameter; original standalone comparisons remain nonconforming" },
      negativeColumns, expectedNegatives, moduleDiagnostics,
      positiveDiagnostics: green.map(diagnostic), redDiagnostics: red.map(diagnostic), columns, pairs, mutants,
      refusals: manifest.refusals, sourceHashes,
      limitations: ["Finite type-only observations of actual Program.printTyped syntax at explicit source environments.",
        "Module compilation, mutual column assignments, and intended missing-member diagnostics are separate results.",
        "Every success fixture requires exact A/E/R/request columns, including optional-record fixtures.",
        "Standalone mutable-array and literal comparisons remain explicit nonconforming observations with their failed reverse assignments.",
        "This fixture consumer neither executes these functions nor creates a ModuleEmission certificate."] }
  } finally { api.close() }
}

const [, , requestPath, responsePath] = process.argv
if (!requestPath || !responsePath) throw new Error("checker.ts <request.json> <response.json>")
const request = JSON.parse(readFileSync(requestPath, "utf8")) as Record<string, unknown>
const repo = resolve(String(request.repo ?? ""))
if (!isAbsolute(repo) || !existsSync(join(repo, "ts/eff/tsconfig.json"))) throw new Error(`target oracle: ${repo} is not a checkout of this repository`)
const answer = request.kind === "p2b-target"
  ? p2bTarget(repo, request as unknown as P2bRequest)
  : request.kind === "truth-widenings"
  ? truthWidenings(repo, request as unknown as TruthWideningRequest)
  : request.kind === "subjects"
  ? { receivers: receivers(repo, request.subjects as string[]) }
  : request.kind === "pairs"
    ? assignability(repo, request.pairs as Pair[])
    : report(repo, String(request.profile), request.queries as Query[])
writeFileSync(responsePath, JSON.stringify(answer))
