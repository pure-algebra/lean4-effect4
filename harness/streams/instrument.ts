import ts from "../../ts/eff/node_modules/typescript/lib/typescript.js"
import { resolve } from "node:path"
const root = resolve(import.meta.dir, "../..")

/** Use syntax positions, so a multiline expression is evaluated once and annotations on
 * nested expression statements stay at the same program point. Never infer expected data. */
export function instrument(row: { id: string; program: string; expected: string[] }, allowNoExpected = false): { code: string; checks: number } {
  const code = row.program
  const parsed = ts.createSourceFile(row.id + ".ts", code, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS)
  const expressions: Array<ts.ExpressionStatement | ts.VariableStatement> = []
  const visit = (node: ts.Node) => {
    if (ts.isExpressionStatement(node) || ts.isVariableStatement(node)) expressions.push(node)
    ts.forEachChild(node, visit)
  }
  visit(parsed)
  const edits: Array<{ start: number; end: number; text: string }> = []
  let checks = 0
  for (const comment of code.matchAll(/\/\/ =>([^\n]*)/g)) {
    const position = comment.index!
    const statement = expressions.filter(node => node.end <= position &&
      code.slice(node.end, position).trim() === "").at(-1)
    if (!statement) throw Error(`expectation has no expression at offset ${position}`)
    const expected = comment[1]!.trim()
    if (expected.length === 0) throw Error("empty expectation")
    let replacement: string
    const label = JSON.stringify(row.id + ":" + ++checks)
    if (ts.isExpressionStatement(statement)) {
      replacement = `__check((${statement.expression.getText(parsed)}), (${expected}), ${label});`
    } else {
      const declarations = statement.declarationList.declarations
      const name = declarations[0]?.name
      if (declarations.length !== 1 || !name || !ts.isIdentifier(name)) throw Error("unsupported annotated binding")
      replacement = `${statement.getText(parsed)}; __check(${name.text}, (${expected}), ${label});`
    }
    edits.push({ start: statement.getStart(parsed), end: position + comment[0].length,
      text: replacement })
  }
  if (checks !== row.expected.length || (checks === 0 && !allowNoExpected)) throw Error("no exact expectations")
  let result = code
  for (const edit of edits.sort((a, b) => b.start - a.start))
    result = result.slice(0, edit.start) + edit.text + result.slice(edit.end)
  result = result.replace(/import\s*\{([^}]+)\}\s*from\s*["']effect["']/g, (_, names: string) =>
    names.split(",").map(name => {
      const [original, alias] = name.trim().split(/\s+as\s+/)
      if (!original || original.startsWith("type ")) throw Error("unsupported root type import")
      if (["pipe", "flow", "identity", "constant", "constVoid"].includes(original))
        return `import { ${name.trim()} } from ${JSON.stringify(resolve(root, "vendor/effect-4.0.0-rc.112/src/Function.ts"))};`
      return `import * as ${alias ?? original} from ${JSON.stringify(resolve(root, "vendor/effect-4.0.0-rc.112/src", original + ".ts"))};`
    }).join("\n"))
  result = result.replace(/(from\s+|import\s*)["']effect(?:\/([^"']+))?["']/g,
    (_, prefix: string, sub: string | undefined) => `${prefix}${JSON.stringify(resolve(root, "vendor/effect-4.0.0-rc.112/src", sub ? sub + ".ts" : "index.ts"))}`)
  return { code: `import { deepStrictEqual as __equal } from "node:assert";
const __seen = new Set<string>();
const __check = (actual: unknown, expected: unknown, label: string) => {
  __equal(actual, expected, label); __seen.add(label);
};
${result}
__equal(__seen.size, ${checks}, "every documented expectation must execute");
`, checks }
}
