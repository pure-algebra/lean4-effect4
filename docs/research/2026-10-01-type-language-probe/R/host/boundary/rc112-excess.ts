// Seat R, question 4: what rc.112 does with the four objects of `Q4Boundary.lean` §5, under its
// default parse options (the host adapter's decode) and under `onExcessProperty: "error"` (the
// strict codec's policy). Run with bun against the pinned effect@4.0.0-rc.112 by absolute path.
import { Schema } from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/index.js"
import pkg from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/package.json"

const User = Schema.Struct({ id: Schema.Number, name: Schema.String, role: Schema.String })
const tryDecode = (input: unknown, strict: boolean): string => {
  try {
    const out = Schema.decodeUnknownSync(User)(input, strict ? { onExcessProperty: "error" } : undefined)
    return JSON.stringify(out)
  } catch (e) {
    return "refused: " + String((e as Error).message).split("\n")[0]
  }
}
const cases: Array<[string, unknown]> = [
  ["wider", { role: "member", id: 2, extra: 1, name: "bob" }],
  ["exact", { name: "bob", role: "member", id: 2 }],
  ["missing", { id: 2, name: "bob" }],
  // a JS object cannot hold a duplicate key; JSON text can, and JSON.parse keeps the last
  ["duplicate (JSON text)", JSON.parse('{"id":2,"name":"bob","role":"member","id":3}')]
]
console.log(JSON.stringify(["effect", pkg.version, "bun", Bun.version]))
for (const [name, input] of cases) {
  console.log(JSON.stringify([name, { default: tryDecode(input, false), strict: tryDecode(input, true) }]))
}
