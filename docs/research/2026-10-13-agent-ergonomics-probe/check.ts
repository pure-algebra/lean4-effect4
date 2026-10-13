// bun --no-install check.ts NAME [ROWS]  — read one program of programs.ts with ts/eff/read.ts and
// print one session request (`open`) on standard output, or the reader's located refusal on
// standard error. ROWS is "todo", "db", "todo+hole" or "none". Pipe the line into
// tools/Drivers/Session.lean.
//
// No bare import: `effect` and `oxc-parser` resolve inside ts/eff/node_modules, through read.ts, at
// the pinned versions. Run with `--no-install` so bun never fetches a package for this folder.
import { readTypeScript, showFailure } from "../../../ts/eff/read.ts"

const [name, rowsName = "none"] = process.argv.slice(2)
const tables = JSON.parse(await Bun.file(new URL("rows.json", import.meta.url)).text())
const hole = { name: "count", spelling: "count", shape: "call", trailing: [], kind: "async",
  request: { _tag: "unit" }, answer: { _tag: "nat" }, error: { _tag: "never" }, requires: [],
  cite: "", typeArgs: [], registration: "external" }
const rows = rowsName === "none" ? [] : rowsName === "todo+hole" ? tables.todo : tables[rowsName]
const table = rowsName === "todo+hole" ? [...rows, hole] : rows
const text = await Bun.file(new URL("programs.ts", import.meta.url)).text()
const prefix = `export const ${name} = `
const line = text.split("\n").find((l) => l.startsWith(prefix))
if (line === undefined) throw new Error(`no program ${name}`)
// A bare expression is one program file (`programExprOf`, ts/eff/read.ts § 2).
const r = readTypeScript(line.slice(prefix.length), "p.ts", table) as
  { _tag: "Success"; success: unknown } | { _tag: "Failure"; failure: Parameters<typeof showFailure>[0] }
if (r._tag === "Failure") {
  console.error(showFailure(r.failure))
  process.exit(1)
}
// The session reads the Schema node's own JSON (arrays for lists), not json.gen.ts `toJson`.
const request: Record<string, unknown> = { op: "open", programJson: r.success }
if (rows.length > 0) request.rowsJson = rows
if (rowsName === "todo+hole") request.holesJson = [hole]
console.log(JSON.stringify(request))
