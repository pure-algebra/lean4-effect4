import assert from "node:assert/strict"
import * as Schema from "effect/Schema"
import * as R from "effect/SchemaRepresentation"

const nat = Schema.Number.check(Schema.isInt(), Schema.isGreaterThanOrEqualTo(0))
const live = R.toRepresentation(nat.ast)
const persisted = R.fromJson(R.toJson(live))
const emit = d => R.toCodeDocument(R.toMultiDocument(d)).codes[0].runtime
const liveCode = emit(live)
let persistedError = ""
try { emit(persisted) } catch (e) { persistedError = e.message }
assert.match(persistedError, /Missing toCode callback/)
assert.throws(() => R.fromRepresentation(persisted, {revivers: []}), /Missing reviver/)
const restored = R.fromRepresentation(persisted, {
  revivers: [Schema.isIntReviver, Schema.isGreaterThanOrEqualToReviver]
})
const restoredCode = emit(R.toRepresentation(restored.ast))
assert.equal(restoredCode, liveCode)
const accepts = v => {
  try { Schema.decodeUnknownSync(restored)(v); return true } catch { return false }
}
const controls = [[0, true], [42, true], [-1, false], [1.5, false], ["42", false]]
for (const [value, expected] of controls) assert.equal(accepts(value), expected)

// These are exact target expressions selected by the inspected prototype arms.
const tuple = Schema.Tuple([Schema.String])
const emittedArray = Schema.Array(Schema.String)
assert.throws(() => Schema.decodeUnknownSync(tuple)([]))
assert.deepEqual(Schema.decodeUnknownSync(emittedArray)([]), [])
assert.throws(() => Schema.Union(Schema.String, Schema.Number))
assert.throws(() => Function("Schema", "return Schema.Struct({ a-b: Schema.String })")(Schema), SyntaxError)
assert.equal(typeof Schema.decodeUnknownSync(Schema.Literal(1))(1), "number")
assert.throws(() => Schema.decodeUnknownSync(Schema.Literal(1))(1n))

console.log(JSON.stringify({ liveCode, persistedError, restoredCode, controls,
  tupleArrayDifference: "empty array rejected by tuple, accepted by emitted array",
  variadicUnion: "throws; rc.112 needs an array",
  bareHyphenProperty: "SyntaxError",
  bigintAsIntLiteral: "accepts number 1, rejects bigint 1n",
  scope: "finite host API probes; no production Lean preservation theorem" }, null, 2))
