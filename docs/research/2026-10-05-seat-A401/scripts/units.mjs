// Seat A401 (2026-10-05). The declarations of each source file, as units with a syntax digest.
//
// Run: bun units.mjs <oxc-parser entry> <root> <out.json> <ext> [file ...]
//
// With no file argument, every file under <root> with the extension is read. For each file the
// output holds a list of units, in source order:
//   { key, kind, start, end, ast }
// A unit is a top-level statement, or a member of a top-level class. `key` is the declared name
// (`forkUnsafe`, `FiberImpl.runLoop`, `get FiberImpl.id`), with `#n` added when a name repeats in the
// file (overload signatures, a namespace beside a constant). `start` and `end` are line numbers.
// `ast` is the SHA-256 of the unit's syntax tree without positions: equal digests mean equal
// syntax, whatever the comments and the layout. Nothing of the input tree is executed.
import { createHash } from "node:crypto"
import { readdirSync, readFileSync, statSync, writeFileSync } from "node:fs"
import { join, relative } from "node:path"

const [oxcEntry, root, outPath, ext, ...only] = process.argv.slice(2)
if (!oxcEntry || !root || !outPath || !ext) {
  console.error("usage: bun units.mjs <oxc-parser entry> <root> <out.json> <ext> [file ...]")
  process.exit(2)
}
const { parseSync } = await import(oxcEntry)

const walk = (dir) => {
  const out = []
  for (const name of readdirSync(dir).sort()) {
    const p = join(dir, name)
    if (statSync(p).isDirectory()) out.push(...walk(p))
    else if (name.endsWith(ext) && !name.endsWith(".d.ts")) out.push(relative(root, p))
  }
  return out
}

const sha = (text) => createHash("sha256").update(text).digest("hex")
const dropPositions = (key, value) =>
  key === "start" || key === "end" ? undefined : typeof value === "bigint" ? `bigint:${value}` : value
const digest = (node) => sha(JSON.stringify(node, dropPositions))

const keyName = (key) =>
  key === null || key === undefined ? "?"
    : key.type === "Identifier" || key.type === "PrivateIdentifier" ? key.name
    : key.type === "Literal" ? String(key.value)
    : key.type === "MemberExpression" && key.object?.name && key.property?.name ? `[${key.object.name}.${key.property.name}]`
    : key.type === "Identifier" ? key.name
    : `[${key.type === "Identifier" ? key.name : key.name ?? key.type}]`

const patternNames = (id) =>
  id.type === "Identifier" ? [id.name]
    : id.type === "ObjectPattern" ? id.properties.flatMap((p) => patternNames(p.value ?? p.argument))
    : id.type === "ArrayPattern" ? id.elements.filter(Boolean).flatMap(patternNames)
    : id.type === "AssignmentPattern" ? patternNames(id.left)
    : id.type === "RestElement" ? patternNames(id.argument)
    : ["?"]

const namesOf = (node) => {
  switch (node.type) {
    case "VariableDeclaration":
      return { kind: node.kind, names: node.declarations.flatMap((d) => patternNames(d.id)) }
    case "FunctionDeclaration":
    case "TSDeclareFunction":
      return { kind: "function", names: [node.id?.name ?? "default"] }
    case "ClassDeclaration":
      return { kind: "class", names: [node.id?.name ?? "default"] }
    case "TSInterfaceDeclaration":
      return { kind: "interface", names: [node.id.name] }
    case "TSTypeAliasDeclaration":
      return { kind: "type", names: [node.id.name] }
    case "TSModuleDeclaration":
      return { kind: "namespace", names: [node.id.name ?? node.id.value ?? "?"] }
    case "TSEnumDeclaration":
      return { kind: "enum", names: [node.id.name] }
    case "ImportDeclaration":
      return { kind: "import", names: [`import ${node.source.value}`] }
    case "ExportAllDeclaration":
      return { kind: "export-all", names: [`export * ${node.source.value}`] }
    case "ExpressionStatement":
      return { kind: "statement", names: ["statement"] }
    default:
      return { kind: node.type, names: [node.type] }
  }
}

const files = only.length > 0 ? only : walk(root)
const out = {}
for (const rel of files) {
  const source = readFileSync(join(root, rel), "utf8")
  const lineStarts = [0]
  for (let i = 0; i < source.length; i++) if (source[i] === "\n") lineStarts.push(i + 1)
  const lineOf = (offset) => {
    let lo = 0, hi = lineStarts.length - 1
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1
      if (lineStarts[mid] <= offset) lo = mid
      else hi = mid - 1
    }
    return lo + 1
  }
  const result = parseSync(rel, source, { lang: ext === ".ts" ? "ts" : "js", sourceType: "module" })
  const units = []
  const seen = new Map()
  const push = (name, kind, node) => {
    const n = (seen.get(name) ?? 0) + 1
    seen.set(name, n)
    units.push({ key: n === 1 ? name : `${name}#${n}`, kind, start: lineOf(node.start), end: lineOf(Math.max(node.start, node.end - 1)), ast: digest(node) })
  }
  for (const statement of result.program.body) {
    let node = statement
    let exported = false
    if (statement.type === "ExportNamedDeclaration" && statement.declaration) {
      node = statement.declaration
      exported = true
    } else if (statement.type === "ExportNamedDeclaration") {
      push(`export {${statement.specifiers.map((s) => s.exported.name ?? s.exported.value).join(",")}}`, "export-list", statement)
      continue
    } else if (statement.type === "ExportDefaultDeclaration") {
      push("default", "export-default", statement)
      continue
    }
    const { kind, names } = namesOf(node)
    const name = names.join(",")
    push(name, (exported ? "export " : "") + kind, statement)
    if (node.type === "ClassDeclaration") {
      for (const member of node.body.body) {
        const prefix = member.kind === "get" ? "get " : member.kind === "set" ? "set " : ""
        const label = member.type === "StaticBlock" ? "static-block" : keyName(member.key)
        push(`${prefix}${name}.${label}`, member.static ? "static member" : "member", member)
      }
    }
  }
  out[rel] = units
}
writeFileSync(outPath, JSON.stringify(out))
console.log(`${Object.keys(out).length} files, ${Object.values(out).reduce((n, u) => n + u.length, 0)} units from ${root}`)
