import assert from "node:assert/strict"
import * as Schema from "effect/Schema"
import * as Representation from "effect/SchemaRepresentation"

const computed = Schema.Struct({ ["a-b"]: Schema.String, ["__proto__"]: Schema.Number })
const entries = Schema.Struct(Object.fromEntries([
  ["a-b", Schema.String], ["__proto__", Schema.Number]
]))
const good = JSON.parse('{"a-b":"ok","__proto__":1}')
const missing = JSON.parse('{"a-b":"ok"}')
const wrong = JSON.parse('{"a-b":"ok","__proto__":"bad"}')
const names = s => s.ast.propertySignatures.map(p => p.name)
const accepts = (s, input) => {
  try { Schema.decodeUnknownSync(s, { onExcessProperty: "error" })(input); return true }
  catch { return false }
}
for (const s of [computed, entries]) {
  assert.deepEqual(names(s), ["a-b", "__proto__"])
  assert.equal(accepts(s, good), true)
  assert.equal(accepts(s, missing), false)
  assert.equal(accepts(s, wrong), false)
  const output = Schema.decodeUnknownSync(s)(good)
  assert.equal(Object.hasOwn(output, "__proto__"), true)
  assert.equal(output["__proto__"], 1)
}
const code = Representation.toCodeDocument(
  Representation.toMultiDocument(Representation.toRepresentation(computed.ast))
).codes[0]
const upstream = Function("Schema", `return (${code.runtime})`)(Schema)
assert.deepEqual(names(upstream), ["a-b"])
assert.equal(accepts(upstream, missing), true)
assert.equal(accepts(upstream, good), false)
console.log(JSON.stringify({
  runtime: code.runtime, Type: code.Type,
  computedFields: names(computed), fromEntriesFields: names(entries),
  upstreamFields: names(upstream),
  upstreamAcceptsMissing: accepts(upstream, missing),
  upstreamAcceptsCompleteUnderStrictOptions: accepts(upstream, good),
  passingAndRejectingControls: "all held"
}, null, 2))
