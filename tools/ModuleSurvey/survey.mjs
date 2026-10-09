/** Deterministic source inventory, not a behavioral or complete call graph. */
import { parseTypeScript, childNodes } from "../../ts/eff/ingest/oxc.ts"
import { readFileSync, readdirSync, writeFileSync, mkdirSync } from "node:fs"
import { resolve, relative, dirname } from "node:path"
import { createHash } from "node:crypto"
import { fileURLToPath } from "node:url"

const digest = (text) => createHash("sha256").update(text).digest("hex")
const node = (x) => x && typeof x === "object" && typeof x.type === "string"
const unexport = (n) => n.type === "ExportNamedDeclaration" && n.declaration ? n.declaration : n
const nameOf = (n) => n?.type === "Identifier" ? n.name : n?.type === "Literal" ? String(n.value) : undefined
function bindings(n) {
  if (!node(n)) return []
  if (n.type === "Identifier") return [n.name]
  if (n.type === "TSParameterProperty") return bindings(n.parameter)
  if (n.type === "RestElement") return bindings(n.argument)
  if (n.type === "AssignmentPattern") return bindings(n.left)
  if (n.type === "ObjectPattern") return n.properties.flatMap(p => bindings(p.value ?? p.argument))
  if (n.type === "ArrayPattern") return n.elements.flatMap(bindings)
  return []
}
function declared(n) {
  n = unexport(n)
  if (n.type === "VariableDeclaration") return n.declarations.flatMap(d => bindings(d.id))
  if (n.type === "FunctionDeclaration" || n.type === "ClassDeclaration") return bindings(n.id)
  return []
}
const typeNode = (n) => n.type.startsWith("TS") && !["TSAsExpression", "TSSatisfiesExpression", "TSNonNullExpression", "TSInstantiationExpression", "TSParameterProperty"].includes(n.type)

export function surveySource(filename, source) {
  const parsed = parseTypeScript(filename, source)
  if (parsed.errors.length) throw new Error(`${filename}: parser refused ${parsed.errors.length} errors`)
  const body = parsed.program.body
  const imports = [], exports = [], localExports = [], definitions = [], calls = [], unresolved = []
  const top = new Map()
  for (const statement of body) {
    if (statement.type === "ImportDeclaration") {
      const valueBindings = statement.importKind === "type" ? [] : statement.specifiers.filter(s => s.importKind !== "type").map(s => ({
        local: s.local.name,
        imported: s.type === "ImportNamespaceSpecifier" ? "*" : s.type === "ImportDefaultSpecifier" ? "default" : nameOf(s.imported)
      }))
      imports.push({ source: statement.source.value, typeOnly: statement.importKind === "type" ||
        (statement.specifiers.length > 0 && valueBindings.length === 0), sideEffect: statement.specifiers.length === 0, bindings: valueBindings })
      for (const b of valueBindings) top.set(b.local, { kind: "import", source: statement.source.value, imported: b.imported })
      continue
    }
    if (statement.source && statement.type.startsWith("Export")) {
      exports.push({ source: statement.source.value, typeOnly: statement.exportKind === "type" ||
        (statement.specifiers?.length > 0 && statement.specifiers.every(s => s.exportKind === "type")) })
    }
    if (statement.type === "ExportNamedDeclaration" && !statement.source && statement.exportKind !== "type") {
      for (const spec of statement.specifiers) if (spec.exportKind !== "type") localExports.push({local:nameOf(spec.local),exported:nameOf(spec.exported)})
    }
    const d = unexport(statement)
    for (const name of declared(d)) {
      top.set(name, { kind: "local", name })
      definitions.push({ name, kind: d.type, directlyExported: statement.type.startsWith("Export"), start: d.start, end: d.end })
    }
  }
  function childScope(env, names) { const next = new Map(env); for (const name of names) next.set(name, { kind: "shadow" }); return next }
  function head(n, env) {
    if (n.type === "Identifier") {
      const found = env.get(n.name)
      if (found?.kind === "import") return { kind: "import", source: found.source, member: found.imported === "*" ? "" : found.imported }
      if (found?.kind === "local") return { kind: "local", member: found.name }
      return undefined
    }
    if (n.type === "MemberExpression" && !n.computed) {
      const base = head(n.object, env), property = nameOf(n.property)
      return base && property ? { ...base, member: [base.member, property].filter(Boolean).join(".") } : undefined
    }
    if (["TSAsExpression", "TSSatisfiesExpression", "TSNonNullExpression", "TSInstantiationExpression", "ChainExpression", "ParenthesizedExpression"].includes(n.type)) return head(n.expression, env)
    return undefined
  }
  function walk(n, env, owner) {
    if (!node(n) || typeNode(n) || n.type === "ImportDeclaration") return
    if (["FunctionDeclaration", "FunctionExpression", "ArrowFunctionExpression"].includes(n.type)) {
      // Parameter defaults run outside the body var scope.
      const parameters = n.params.flatMap(bindings)
      if (n.type === "FunctionExpression") parameters.push(...bindings(n.id))
      const parameterScope = childScope(env,parameters)
      for (const p of n.params) walk(p,parameterScope,owner)
      const names = []
      function vars(x) {
        if (!node(x) || typeNode(x)) return
        if (x !== n.body && ["FunctionDeclaration", "FunctionExpression", "ArrowFunctionExpression"].includes(x.type)) return
        if (x.type === "VariableDeclaration" && x.kind === "var") names.push(...declared(x))
        for (const child of childNodes(x)) vars(child)
      }
      vars(n.body)
      walk(n.body, childScope(parameterScope,names), owner)
      return
    }
    if (n.type === "ClassExpression" && n.id) {
      if (n.superClass) walk(n.superClass, env, owner)
      walk(n.body, childScope(env, bindings(n.id)), owner)
      return
    }
    if (n.type === "SwitchStatement") {
      walk(n.discriminant, env, owner)
      const local = childScope(env,n.cases.flatMap(c=>c.consequent.flatMap(declared)))
      for (const c of n.cases) {
        if (c.test) walk(c.test, local, owner)
        for (const statement of c.consequent) walk(statement,local,owner)
      }
      return
    }
    if (n.type === "MethodDefinition" || n.type === "PropertyDefinition") {
      if (n.computed) walk(n.key,env,owner)
      const method = !n.computed ? nameOf(n.key) : undefined
      if (n.value) walk(n.value, env, method ? `${owner}.${method}` : owner)
      return
    }
    if (n.type === "Property" && (n.method || ["FunctionExpression", "ArrowFunctionExpression"].includes(n.value?.type))) {
      if (n.computed) walk(n.key,env,owner)
      const method = !n.computed ? nameOf(n.key) : undefined
      walk(n.value, env, method ? `${owner}.${method}` : owner)
      return
    }
    if (n.type === "BlockStatement") {
      const local = childScope(env, n.body.flatMap(declared))
      for (const child of n.body) walk(child, local, owner)
      return
    }
    if (n.type === "CatchClause") { walk(n.body, childScope(env, bindings(n.param)), owner); return }
    if (["ForStatement", "ForOfStatement", "ForInStatement"].includes(n.type)) {
      const local = childScope(env, declared(n.init ?? n.left ?? {type:"EmptyStatement"}))
      for (const child of childNodes(n)) walk(child, local, owner)
      return
    }
    if (n.type === "CallExpression" || n.type === "NewExpression") {
      const target = head(n.callee, env)
      const location = { owner, start: n.start, end: n.end }
      if (target) calls.push({ ...location, ...target, construction: n.type === "NewExpression" })
      else unresolved.push({ ...location, expression: source.slice(n.callee.start, n.callee.end).slice(0, 100) })
    }
    for (const child of childNodes(n)) walk(child, env, owner)
  }
  for (const statement of body) {
    const d = unexport(statement)
    if (d.type === "VariableDeclaration") {
      for (const entry of d.declarations) {
        const owner = bindings(entry.id).join(",") || "<destructuring>"
        walk(entry.id,top,owner)
        if (entry.init) walk(entry.init,top,owner)
      }
    } else walk(d, top, nameOf(d.id) ?? "<module>")
  }
  return { file: filename, sha256: digest(source), imports, reexports: exports, localExports, definitions, calls, unresolved }
}
function files(folder) {
  return readdirSync(folder, { withFileTypes: true }).flatMap(e => e.isDirectory() ? files(resolve(folder,e.name)) : e.name.endsWith(".ts") ? [resolve(folder,e.name)] : []).sort()
}
export function components(nodes, edges) {
  const adjacency = new Map(nodes.map(n => [n, new Set()]))
  for (const e of edges) if (e.internal) adjacency.get(e.from).add(e.to)
  const index = new Map(), low = new Map(), stack = [], onStack = new Set(), result = []
  let next = 0
  function visit(n) {
    index.set(n,next); low.set(n,next++); stack.push(n); onStack.add(n)
    for (const m of adjacency.get(n)) {
      if (!index.has(m)) { visit(m); low.set(n,Math.min(low.get(n),low.get(m))) }
      else if (onStack.has(m)) low.set(n,Math.min(low.get(n),index.get(m)))
    }
    if (low.get(n) === index.get(n)) {
      const group = []; let m
      do { m=stack.pop(); onStack.delete(m); group.push(m) } while (m!==n)
      result.push(group.sort())
    }
  }
  for (const n of nodes) if (!index.has(n)) visit(n)
  return result.sort((a,b)=>b.length-a.length || a[0].localeCompare(b[0]))
}
export function surveyTree(root) {
  const modules = files(root).map(path => surveySource(relative(root,path), readFileSync(path,"utf8")))
  const known = new Set(modules.map(m => m.file))
  const target = (file, spec) => spec.startsWith(".") ? relative(root, resolve(root, dirname(file), spec)).replace(/\.js$/, ".ts") : spec
  const edges = modules.flatMap(m => [...m.imports.filter(i => !i.typeOnly).map(i => ({...i, kind:"import"})),
    ...m.reexports.filter(e => !e.typeOnly).map(e => ({...e, kind:"reexport"}))].map(i => ({ from:m.file, to:target(m.file,i.source), kind:i.kind, internal:known.has(target(m.file,i.source)) })))
  const helpers = new Map()
  for (const m of modules) for (const c of m.calls) if (c.kind === "import") {
    const key = `${target(m.file,c.source)}#${c.member}`
    const item = helpers.get(key) ?? {target:key, modules:new Set(), operations:new Set(), sites:0}
    item.modules.add(m.file); item.operations.add(`${m.file}#${c.owner}`); item.sites++; helpers.set(key,item)
  }
  const shared = [...helpers.values()].map(x => ({target:x.target, modules:[...x.modules].sort(), operations:[...x.operations].sort(), sites:x.sites})).sort((a,b) => b.modules.length-a.modules.length || b.sites-a.sites || a.target.localeCompare(b.target))
  return { format:"effect4-module-survey-v1", parser:"oxc-parser via ts/eff/ingest/oxc.ts", scope:"Syntactic non-type import and reexport declarations, plus direct call sites owned by top declarations or class methods. Inferred type-only usage, dynamic dispatch, nested helper targets, aliases, execution order and behavior are not resolved.", counts:{modules:modules.length, valueEdges:edges.length, directCalls:modules.reduce((n,m)=>n+m.calls.length,0), unresolvedCalls:modules.reduce((n,m)=>n+m.unresolved.length,0)}, components:components([...known],edges), edges, sharedHelpers:shared, modules }
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const [root, output, summary] = process.argv.slice(2)
  if (!root || !output) throw new Error("Usage: bun tools/ModuleSurvey/survey.mjs SOURCE_ROOT OUTPUT_JSON [SUMMARY_JSON]")
  const report = surveyTree(resolve(root))
  mkdirSync(dirname(resolve(output)), {recursive:true})
  writeFileSync(output, JSON.stringify(report,null,2)+"\n")
  if (summary) {
    const focus = new Set(["Ref.ts", "Queue.ts", "Pull.ts", "Channel.ts", "Stream.ts", "Sink.ts", "PubSub.ts", "SynchronizedRef.ts", "Pool.ts", "Semaphore.ts", "PartitionedSemaphore.ts", "SubscriptionRef.ts", "ScopedRef.ts", "RcRef.ts", "RcMap.ts", "Cache.ts"])
    const overview = { format:"effect4-module-survey-summary-v1", scope:report.scope, counts:report.counts,
      sourceHashes:Object.fromEntries(report.modules.map(m=>[m.file,m.sha256])),
      parserEntryHash:digest(readFileSync(new URL("../../ts/eff/ingest/oxc.ts",import.meta.url))),
      parserVersion:JSON.parse(readFileSync(new URL("../../ts/eff/node_modules/oxc-parser/package.json",import.meta.url))).version,
      surveyHash:digest(readFileSync(fileURLToPath(import.meta.url))),
      reportHash:digest(readFileSync(output)), components:report.components, edges:report.edges,
      sharedHelpers:report.sharedHelpers.filter(h=>h.modules.filter(m=>focus.has(m)).length>=3),
      focus:report.modules.filter(m=>focus.has(m.file)) }
    mkdirSync(dirname(resolve(summary)),{recursive:true})
    writeFileSync(summary,JSON.stringify(overview,null,2)+"\n")
  }
  console.log(JSON.stringify(report.counts))
}
