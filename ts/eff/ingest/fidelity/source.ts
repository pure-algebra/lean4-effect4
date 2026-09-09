import ts from "typescript"
/** Inspect module dependencies, including re-exports and dynamic import/require.
 * This is fidelity eligibility, never a third recognition engine. */
export function sourceModule(source: string, filename: string) {
  const tree = ts.createSourceFile(filename, source, ts.ScriptTarget.Latest, false, filename.endsWith(".tsx") ? ts.ScriptKind.TSX : ts.ScriptKind.TS)
  const foreign = new Set<string>()
  const dependency = (x: ts.Node | undefined) => {
    const name = x && ts.isStringLiteral(x) ? x.text : "<computed module>"
    if (name !== "effect" && !name.startsWith("effect/")) foreign.add(name)
  }
  const visit = (n: ts.Node) => {
    if (ts.isImportDeclaration(n)) dependency(n.moduleSpecifier)
    else if (ts.isExportDeclaration(n) && n.moduleSpecifier) dependency(n.moduleSpecifier)
    else if (ts.isImportEqualsDeclaration(n)) dependency(ts.isExternalModuleReference(n.moduleReference) ? n.moduleReference.expression : undefined)
    else if (ts.isCallExpression(n) && (n.expression.kind === ts.SyntaxKind.ImportKeyword || ts.isIdentifier(n.expression) && n.expression.text === "require")) dependency(n.arguments[0])
    ts.forEachChild(n, visit)
  }
  visit(tree)
  return {
    foreign: [...foreign].sort(),
    expose(name: string, occurrence = 0, span?: { readonly start: number; readonly end: number }): { source: string; name: string } {
      if (name === "default" && tree.statements.some(s => ts.isExportAssignment(s))) return { source, name }
      let alias = "__effect4IngestSelected"
      while (source.includes(alias)) alias += "_"
      if (name.includes("#") && span) {
        for (const statement of tree.statements) {
          if (!ts.isExpressionStatement(statement) || !ts.isCallExpression(statement.expression)) continue
          const argument = statement.expression.arguments.find(a => a.getStart(tree) === span.start && a.end === span.end)
          if (!argument) continue
          // The I3 unit is the argument. Its entry operation is supplied by the recorder.
          // Evaluate that original argument once in its original module scope.
          const replacement = `export const ${alias} = (${source.slice(span.start, span.end)});`
          return { source: source.slice(0, statement.getStart(tree)) + replacement + source.slice(statement.end), name: alias }
        }
      }
      const declaration = tree.statements.flatMap(s => ts.isVariableStatement(s) ? [...s.declarationList.declarations] : []).filter(d => ts.isIdentifier(d.name) && d.name.text === name)[occurrence]
      if (!declaration || !ts.isIdentifier(declaration.name)) throw new Error(`cannot expose original unit without changing execution: ${name}`)
      return { source: source + `\nexport { ${declaration.name.text} as ${alias} }\n`, name: alias }
    }
  }
}
