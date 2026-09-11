/** Declaration ranges, including their doc comments, from the pinned TypeScript parser. */
import ts from "../../ts/eff/node_modules/typescript/lib/typescript.js"
import { readFileSync } from "node:fs"

const owners = Object.fromEntries(process.argv.slice(2).map(path => {
  const source = ts.createSourceFile(path, readFileSync(path, "utf8"), ts.ScriptTarget.Latest, true)
  const entries = source.statements.flatMap(node => {
    if (!ts.canHaveModifiers(node) || !ts.getModifiers(node)?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) return []
    const name = ts.isVariableStatement(node) ? node.declarationList.declarations[0]?.name
      : ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node) || ts.isFunctionDeclaration(node)
        || ts.isClassDeclaration(node) ? node.name : undefined
    return name ? [{ start: node.getFullStart(), end: node.end, name: name.getText(source) }] : []
  })
  return [path, entries]
}))
console.log(JSON.stringify(owners))
