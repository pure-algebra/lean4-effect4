import type { Argument, Expression, Node } from "oxc-parser"
import { childNodes, parseTypeScript } from "../oxc.ts"
/** Inspect module dependencies, including re-exports and dynamic import/require.
 * This is fidelity eligibility, never a third recognition engine. It reads the ingest's one parse
 * (`parseTypeScript`, decisions row 168), as TypeScript's `createSourceFile` tree held the same
 * source: a dynamic `import(x)` is a call on the `import` keyword there, and an `export` wrapper
 * there is a modifier of the declaration it wraps. */
export function sourceModule(source: string, filename: string) {
  const tree = parseTypeScript(filename, source).program
  const foreign = new Set<string>()
  const dependency = (x: Argument | Expression | null | undefined) => {
    const name = x && x.type === "Literal" && typeof x.value === "string" ? x.value : "<computed module>"
    if (name !== "effect" && !name.startsWith("effect/")) foreign.add(name)
  }
  const visit = (n: Node) => {
    if (n.type === "ImportDeclaration") dependency(n.source)
    else if ((n.type === "ExportNamedDeclaration" || n.type === "ExportAllDeclaration") && n.source) dependency(n.source)
    else if (n.type === "TSImportEqualsDeclaration") dependency(n.moduleReference.type === "TSExternalModuleReference" ? n.moduleReference.expression : undefined)
    else if (n.type === "ImportExpression") dependency(n.source)
    else if (n.type === "CallExpression" && n.callee.type === "Identifier" && n.callee.name === "require") dependency(n.arguments[0])
    for (const child of childNodes(n)) visit(child)
  }
  visit(tree)
  // The top-level statements as the TypeScript AST lists them: a declaration under `export` is
  // itself; `export default <expression>` and `export =` are export assignments.
  const statements = tree.body.map(s => s.type === "ExportNamedDeclaration" && s.declaration ? s.declaration : s)
  const exportAssignment = tree.body.some(s => s.type === "TSExportAssignment" || s.type === "ExportDefaultDeclaration" &&
    s.declaration.type !== "FunctionDeclaration" && s.declaration.type !== "TSDeclareFunction" && s.declaration.type !== "ClassDeclaration" && s.declaration.type !== "TSInterfaceDeclaration")
  return {
    foreign: [...foreign].sort(),
    expose(name: string, occurrence = 0, span?: { readonly start: number; readonly end: number }): { source: string; name: string } {
      if (name === "default" && exportAssignment) return { source, name }
      let alias = "__effect4IngestSelected"
      while (source.includes(alias)) alias += "_"
      if (name.includes("#") && span) {
        for (const statement of statements) {
          if (statement.type !== "ExpressionStatement") continue
          const call = statement.expression.type === "ChainExpression" ? statement.expression.expression : statement.expression
          if (call.type !== "CallExpression") continue
          const argument = call.arguments.find(a => a.start === span.start && a.end === span.end)
          if (!argument) continue
          // The I3 unit is the argument. Its entry operation is supplied by the recorder.
          // Evaluate that original argument once in its original module scope.
          const replacement = `export const ${alias} = (${source.slice(span.start, span.end)});`
          return { source: source.slice(0, statement.start) + replacement + source.slice(statement.end), name: alias }
        }
      }
      const declaration = statements.flatMap(s => s.type === "VariableDeclaration" ? [...s.declarations] : []).filter(d => d.id.type === "Identifier" && d.id.name === name)[occurrence]
      if (!declaration || declaration.id.type !== "Identifier") throw new Error(`cannot expose original unit without changing execution: ${name}`)
      return { source: source + `\nexport { ${declaration.id.name} as ${alias} }\n`, name: alias }
    }
  }
}
