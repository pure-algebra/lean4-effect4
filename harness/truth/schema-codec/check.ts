import assert from "node:assert/strict"
import { pathToFileURL } from "node:url"
import { Cause, Exit, Option, Result, Schema } from "effect"
import effectPackage from "effect/package.json"

assert.equal(effectPackage.version, "4.0.0-rc.112")
const input = process.argv[2]
if (!input) throw new Error("expected a fresh Lean output module")
const { default: encoded, refusals } = await import(pathToFileURL(input).href)
if (typeof encoded !== "object" || encoded === null || Array.isArray(encoded)) {
  throw new Error("Lean codec output is not an object")
}

if (typeof refusals !== "object" || refusals === null || Array.isArray(refusals)) {
  throw new Error("Lean refusal output is not an object")
}

const cause = Cause.fromReasons([
  Cause.makeFailReason("bad"),
  Cause.makeDieReason({ user: 7 }),
  Cause.makeInterruptReason(undefined),
  Cause.makeInterruptReason(9)
])
let checked = 0
const names: string[] = []
function check<S extends Schema.ConstraintCodec<unknown, unknown>>(name: string, schema: S, value: S["Type"]) {
  const codec = Schema.toCodecJson(schema)
  const host = Schema.encodeSync(codec)(value)
  assert.deepEqual(encoded[name], host, `${name}: Lean/rc.112 encoding differs`)
  const recovered = Schema.decodeUnknownSync(codec)(encoded[name])
  assert.deepEqual(Schema.encodeSync(codec)(recovered), host, `${name}: host round trip differs`)
  names.push(name)
  checked++
}

check("unit", Schema.Void, undefined)
check("bool", Schema.Boolean, true)
check("nat", Schema.Int.check(Schema.isGreaterThanOrEqualTo(0)), 42)
check("string", Schema.String, "λ🙂")
check("literal", Schema.Literal("User"), "User")
check("pair", Schema.Tuple([Schema.Number, Schema.String]), [3, "x"])
check("list", Schema.Array(Schema.Boolean), [true, false])
check("none", Schema.Option(Schema.Number), Option.none())
check("some", Schema.Option(Schema.Number), Option.some(7))
check("resultFailure", Schema.Result(Schema.Boolean, Schema.String), Result.fail("bad"))
check("resultSuccess", Schema.Result(Schema.Boolean, Schema.String), Result.succeed(true))
check("exitSuccess", Schema.Exit(Schema.Boolean, Schema.String, Schema.Defect()), Exit.succeed(true))
check("exitFailure", Schema.Exit(Schema.Boolean, Schema.String, Schema.Defect()), Exit.failCause(cause))
check("cause", Schema.Cause(Schema.String, Schema.Defect()), cause)
check("emptyCause", Schema.Cause(Schema.Never, Schema.Defect()), Cause.empty)
check("union", Schema.Union([Schema.String, Schema.Number]), 4)
check("nested", Schema.Array(Schema.Option(Schema.Result(Schema.Boolean, Schema.String))),
  [Option.some(Result.succeed(true)), Option.none()])
const nat = Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))
const person = Schema.Struct({ name: Schema.String, nickname: Schema.optionalKey(Schema.Option(Schema.String)) })
const slot = Schema.Struct({ slot: Schema.optionalKey(Schema.Void) })
const triple = Schema.Tuple([nat, Schema.String, Schema.Boolean])
const ada = { name: "Ada" }
const adaNone = { name: "Ada", nickname: Option.none<string>() }
const adaSome = { name: "Ada", nickname: Option.some("A") }
check("recordAbsent", person, ada)
check("recordNone", person, adaNone)
check("recordSome", person, adaSome)
check("recordVoidAbsent", slot, {})
check("recordVoidPresent", slot, { slot: undefined })
check("recordKeys", Schema.Struct({ "": Schema.String, ["__proto__"]: nat, "a-b": Schema.Boolean }),
  { "": "empty", ["__proto__"]: 7, "a-b": true })
check("mapEmpty", Schema.Record(Schema.String, Schema.Never), {})
check("mapKeys", Schema.Record(Schema.String, nat),
  { "2": 2, "10": 10, ["__proto__"]: 7, "a-b": 3, "λ🙂": 4 })
check("mapRecords", Schema.Record(Schema.String, person), { ["__proto__"]: ada, "a-b": adaNone })
check("tuple0", Schema.Tuple([]), [])
check("tuple1", Schema.Tuple([nat]), [7])
check("tuple2", Schema.Tuple([nat, Schema.String]), [7, "x"])
check("tuple3", triple, [7, "x", true])
check("nestedRecordMapTuple", Schema.Struct({ rows: Schema.Record(Schema.String,
  Schema.Tuple([person, Schema.Option(nat), Schema.Boolean])) }),
  { rows: { ["__proto__"]: [adaSome, Option.some(9), true], "a-b": [ada, Option.none(), false] } })
check("nestedTupleRecordMap", Schema.Tuple([slot, Schema.Record(Schema.String, Schema.Option(Schema.String)),
  Schema.Tuple([])]), [{ slot: undefined }, { "a-b": Option.none(), ["__proto__"]: Option.some("ok") }, []])
assert.deepEqual(Object.keys(encoded).sort(), names.sort(), "uncompared or missing Lean fixture")

// Presence and prototype-sensitive names survive both encoding and host decoding.
assert.equal(Object.hasOwn(encoded.recordAbsent, "nickname"), false)
assert.equal(Object.hasOwn(encoded.recordNone, "nickname"), true)
assert.equal(Object.hasOwn(encoded.recordVoidAbsent, "slot"), false)
assert.equal(Object.hasOwn(encoded.recordVoidPresent, "slot"), true)
assert.equal(encoded.recordVoidPresent.slot, null)
const slotCodec = Schema.toCodecJson(slot)
assert.equal(Object.hasOwn(Schema.decodeUnknownSync(slotCodec)(encoded.recordVoidAbsent), "slot"), false)
const presentSlot = Schema.decodeUnknownSync(slotCodec)(encoded.recordVoidPresent)
assert.equal(Object.hasOwn(presentSlot, "slot"), true)
assert.equal(presentSlot.slot, undefined)
for (const value of [encoded.recordKeys, encoded.mapKeys, encoded.mapRecords, encoded.nestedRecordMapTuple.rows]) {
  assert.equal(Object.hasOwn(value, "__proto__"), true)
  assert.equal(Object.getPrototypeOf(value), Object.prototype)
}

const refusalNames: string[] = []
function checkRefusal<S extends Schema.ConstraintCodec<unknown, unknown>>(name: string, schema: S) {
  const fixture = refusals[name]
  assert.equal(fixture.refused, true, `${name}: Lean must refuse`)
  // Strict excess-property handling matches this Lean record boundary.
  assert.throws(() => Schema.decodeUnknownSync(Schema.toCodecJson(schema),
    { onExcessProperty: "error" })(fixture.input), `${name}: rc.112 must refuse`)
  refusalNames.push(name)
}
checkRefusal("recordMissing", person)
checkRefusal("recordExtra", person)
checkRefusal("recordWrong", person)
checkRefusal("mapWrong", Schema.Record(Schema.String, nat))
checkRefusal("tuple0Long", Schema.Tuple([]))
checkRefusal("tuple1Short", Schema.Tuple([nat]))
checkRefusal("tuple1Long", Schema.Tuple([nat]))
checkRefusal("tuple3Short", triple)
checkRefusal("tuple3Long", triple)
checkRefusal("tuple3Wrong", triple)

// Default host decoding discards extra fields; the Lean codec refuses them.
assert.deepEqual(Schema.decodeUnknownSync(Schema.toCodecJson(person))(refusals.recordExtra.input), ada)
// JSON text parsing collapses duplicate keys before Schema sees an object.
// These observations document the boundary difference, not matching raw inputs.
for (const [name, schema, text, expected] of [
  ["recordDuplicate", person, '{"name":"Ada","name":"Grace"}', { name: "Grace" }],
  ["mapDuplicate", Schema.Record(Schema.String, nat), '{"x":1,"x":2}', { x: 2 }]
] as const) {
  assert.equal(refusals[name].refused, true, `${name}: Lean entry-list input must refuse`)
  assert.deepEqual(refusals[name].input, JSON.parse(text), `${name}: host object conversion keeps the last key`)
  assert.deepEqual(Schema.decodeUnknownSync(Schema.toCodecJson(schema))(JSON.parse(text)), expected)
  refusalNames.push(name)
}
assert.deepEqual(Object.keys(refusals).sort(), refusalNames.sort(), "uncompared or missing Lean refusal")

// Negative controls catch the two incorrect shapes in the original specification.
assert.throws(() => Schema.decodeUnknownSync(Schema.toCodecJson(
  Schema.Result(Schema.Boolean, Schema.String)))({ _tag: "Success", value: true }))
assert.throws(() => Schema.decodeUnknownSync(Schema.toCodecJson(
  Schema.Cause(Schema.String, Schema.Defect())))({ reasons: [] }))
console.log(`PASS schema-codec: ${checked} fresh Lean/rc.112 comparisons, ${checked} host round trips, 10 matching refusals, 2 legacy negative controls, 3 explicit boundary differences`)
