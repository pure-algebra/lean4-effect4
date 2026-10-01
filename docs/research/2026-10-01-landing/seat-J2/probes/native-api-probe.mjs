// Seat J2, step 1: does the pinned preview's JS API (`unstable/sync`, tsgo 7.0.0-dev.20260629.1) give a
// file's syntactic diagnostics and its tree, under node and under bun? Runs tsgo 7 only.
const pkg = "/Users/pooks/Dev/lean4-effect4-seat-J2/ts/eff/node_modules/@typescript/native-preview"
const { API } = await import(pkg + "/dist/api/sync/api.js")
const { createVirtualFileSystem } = await import(pkg + "/dist/api/fs.js")
const { SyntaxKind } = await import(pkg + "/dist/ast/index.js")
const runtime = globalThis.Bun ? `bun ${Bun.version}` : `node ${process.versions.node}`
const files = {
  "/v/tsconfig.json": JSON.stringify({ compilerOptions: { noLib: true, types: [], noResolve: true }, files: ["good.ts", "bad.ts"] }),
  "/v/good.ts": 'import { Effect } from "effect"\nexport const main = Effect.succeed((1))\n',
  "/v/bad.ts": "const x = ;\n",
}
let api
try {
  api = new API({ cwd: "/v", fs: createVirtualFileSystem(files) })
  const snapshot = api.updateSnapshot({ openProjects: ["/v/tsconfig.json"] })
  const project = snapshot.getProject("/v/tsconfig.json")
  for (const name of ["/v/good.ts", "/v/bad.ts"]) {
    const d = project.program.getSyntacticDiagnostics(name)
    console.log(runtime, name, "syntactic:", JSON.stringify(d.map(x => ({ code: x.code, pos: x.pos, end: x.end, text: x.text }))))
  }
  const sf = project.program.getSourceFile("/v/good.ts")
  const kinds = []
  const visit = n => { kinds.push(SyntaxKind[n.kind] + "@" + n.pos + "-" + n.end); n.forEachChild(visit) }
  visit(sf)
  console.log(runtime, "good.ts tree:", kinds.join(" "))
  const st = sf.statements[1]
  console.log(runtime, "statement 1 modifiers:", st.modifiers?.map(m => SyntaxKind[m.kind]).join(","), "keys:", Object.keys(Object.getPrototypeOf(st)).slice(0, 12).join(","))
  console.log(runtime, "has getStart:", typeof st.getStart, "getText:", typeof st.getText, "text slice:", JSON.stringify(sf.text.slice(st.pos, st.end)))
} catch (e) { console.log(runtime, "FAILED:", e && e.stack || String(e)); process.exitCode = 1 }
finally { try { api?.close() } catch {} }
