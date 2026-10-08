import assert from "node:assert/strict"
import { pathToFileURL } from "node:url"
import { Cause, Exit, Option, Result, Schema } from "effect"
import effectPackage from "effect/package.json"

assert.equal(effectPackage.version, "4.0.0-rc.112")
const input = process.argv[2]
if (!input) throw new Error("expected a fresh Lean output module")
const { default: encoded, refusals, numericDecodings, encodingRefusals } = await import(pathToFileURL(input).href)
if (typeof encoded !== "object" || encoded === null || Array.isArray(encoded)) {
  throw new Error("Lean codec output is not an object")
}

if (typeof refusals !== "object" || refusals === null || Array.isArray(refusals)) {
  throw new Error("Lean refusal output is not an object")
}
for (const [name, value] of Object.entries({ numericDecodings, encodingRefusals })) {
  assert.ok(typeof value === "object" && value !== null && !Array.isArray(value), `${name}: missing Lean observations`)
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

interface NumericDecoding {
  input: number
  decoded: boolean
  reencoded: number
}
// The independent datum decoded by Lean must be the actual datum encoded by rc.112.
// Strict equality uses Object.is, so corrupting -0 to +0 cannot pass.
function validateNumeric(name: string, fixtures: Record<string, NumericDecoding>, host: unknown) {
  assert.ok(Object.hasOwn(fixtures, name), `${name}: missing Lean decoder observation`)
  const fixture = fixtures[name]!
  assert.equal(fixture.decoded, true, `${name}: public Lean decoder must recover the stored value`)
  assert.equal(fixture.input, host, `${name}: host encoding differs from Lean decoder input`)
  assert.equal(fixture.reencoded, host, `${name}: Lean decoder reencoding differs`)
}
const numericNames: string[] = []
function checkNumeric(name: string, schema: typeof Schema.Int | typeof Schema.Number, value: number) {
  check(name, schema, value)
  const codec = Schema.toCodecJson(schema)
  const host = Schema.encodeSync(codec)(value)
  validateNumeric(name, numericDecodings, host)
  assert.equal(Schema.decodeUnknownSync(codec)(encoded[name]), value, `${name}: host decoder changed the numeric datum`)
  numericNames.push(name)
}
checkNumeric("intZero", Schema.Int, 0)
checkNumeric("intPositive", Schema.Int, 404)
checkNumeric("intNegative", Schema.Int, -15)
checkNumeric("intPositiveBound", Schema.Int, Number.MAX_SAFE_INTEGER)
checkNumeric("intNegativeBound", Schema.Int, -Number.MAX_SAFE_INTEGER)
checkNumeric("numberZero", Schema.Number, 0)
checkNumeric("numberPositive", Schema.Number, 3)
checkNumeric("numberNegative", Schema.Number, -3)
checkNumeric("numberPositiveFraction", Schema.Number, 0.5)
checkNumeric("numberNegativeFraction", Schema.Number, -0.5)
checkNumeric("numberNegativeZero", Schema.Number, -0)
checkNumeric("numberPositiveBound", Schema.Number, Number.MAX_SAFE_INTEGER)
checkNumeric("numberNegativeBound", Schema.Number, -Number.MAX_SAFE_INTEGER)
checkNumeric("numberAboveBound", Schema.Number, 2 ** 53)
checkNumeric("numberBelowBound", Schema.Number, -(2 ** 53))
checkNumeric("numberLargePositive", Schema.Number, 2 ** 60)
checkNumeric("numberLargeNegative", Schema.Number, -(2 ** 60))
assert.deepEqual(Object.keys(numericDecodings).sort(), numericNames.sort(), "uncompared or missing Lean numeric decoder fixture")

// Mutants reach the same checker as the host observations, after the positive cases pass.
let negativeControls = 0
const omittedNumeric = { ...numericDecodings }
delete omittedNumeric.intNegative
assert.throws(() => validateNumeric("intNegative", omittedNumeric, -15), /missing Lean decoder observation/)
negativeControls++
assert.throws(() => validateNumeric("intNegative", {
  ...numericDecodings, intNegative: { ...numericDecodings.intNegative, input: 15 }
}, -15), /host encoding differs/)
negativeControls++
assert.throws(() => validateNumeric("numberNegativeZero", {
  ...numericDecodings, numberNegativeZero: { ...numericDecodings.numberNegativeZero, reencoded: 0 }
}, -0), /Lean decoder reencoding differs/)
negativeControls++
assert.throws(() => validateNumeric("numberPositiveFraction", {
  ...numericDecodings, numberPositiveFraction: { ...numericDecodings.numberPositiveFraction, decoded: false }
}, 0.5), /public Lean decoder must recover/)
negativeControls++
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
let matchingRefusals = 0
let boundaryDifferences = 3 // excess-property defaults and the two duplicate-key inputs
function checkRefusal<S extends Schema.ConstraintCodec<unknown, unknown>>(name: string, schema: S) {
  const fixture = refusals[name]
  assert.equal(fixture.refused, true, `${name}: Lean must refuse`)
  // Strict excess-property handling matches this Lean record boundary.
  assert.throws(() => Schema.decodeUnknownSync(Schema.toCodecJson(schema),
    { onExcessProperty: "error" })(fixture.input), `${name}: rc.112 must refuse`)
  refusalNames.push(name)
  matchingRefusals++
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
checkRefusal("intAboveBound", Schema.Int)
checkRefusal("intBelowBound", Schema.Int)
checkRefusal("intPositiveFraction", Schema.Int)
checkRefusal("intNegativeFraction", Schema.Int)
checkRefusal("intNaN", Schema.Int)
checkRefusal("intPositiveInfinity", Schema.Int)
checkRefusal("intNegativeInfinity", Schema.Int)
checkRefusal("intWrongType", Schema.Int)
checkRefusal("numberWrongType", Schema.Number)

const encodingRefusalNames: string[] = []
let matchingEncoderRefusals = 0
for (const [name, schema, value] of [
  ["intAboveBound", Schema.Int, 2 ** 53],
  ["intBelowBound", Schema.Int, -(2 ** 53)],
  ["intPositiveFraction", Schema.Int, 0.5],
  ["intNegativeFraction", Schema.Int, -0.5],
  ["intNaN", Schema.Int, NaN],
  ["intPositiveInfinity", Schema.Int, Infinity],
  ["intNegativeInfinity", Schema.Int, -Infinity],
  ["intWrongType", Schema.Int, "1"],
  ["numberWrongType", Schema.Number, "1"]
] as const) {
  assert.equal(encodingRefusals[name], true, `${name}: Lean encoder must refuse`)
  const codec = Schema.toCodecJson(schema)
  const encodeUnknown = Schema.encodeUnknownSync(codec)
  assert.throws(() => encodeUnknown(value), `${name}: rc.112 encoder must refuse`)
  encodingRefusalNames.push(name)
  matchingEncoderRefusals++
}

// The integer codec excludes -0 even though rc.112's isInt accepts it.
assert.equal(refusals.intNegativeZero.refused, true)
assert.equal(encodingRefusals.intNegativeZero, true)
assert.equal(refusals.intNegativeZero.input, -0)
const intCodec = Schema.toCodecJson(Schema.Int)
assert.equal(Schema.decodeUnknownSync(intCodec)(refusals.intNegativeZero.input), -0)
assert.equal(Schema.encodeSync(intCodec)(-0), -0)
refusalNames.push("intNegativeZero")
encodingRefusalNames.push("intNegativeZero")
boundaryDifferences++

// NaN and infinities stay outside the Lean number codec. The host writes named strings.
const numberCodec = Schema.toCodecJson(Schema.Number)
for (const [name, value, text] of [
  ["numberNaN", NaN, "NaN"],
  ["numberPositiveInfinity", Infinity, "Infinity"],
  ["numberNegativeInfinity", -Infinity, "-Infinity"]
] as const) {
  assert.equal(refusals[name].refused, true, `${name}: Lean decoder must refuse`)
  assert.equal(refusals[name].input, value, `${name}: raw datum changed`)
  assert.equal(encodingRefusals[name], true, `${name}: Lean encoder must refuse`)
  assert.equal(Schema.encodeSync(numberCodec)(value), text)
  assert.equal(Schema.decodeUnknownSync(numberCodec)(text), value)
  refusalNames.push(name)
  encodingRefusalNames.push(name)
  boundaryDifferences++
}
// No JavaScript number can carry these exact Lean integer magnitudes. Rounding precedes Schema.
for (const [name, magnitude] of [
  ["numberInexactPositive", 9007199254740993n],
  ["numberInexactNegative", -9007199254740993n]
] as const) {
  assert.equal(encodingRefusals[name], true, `${name}: Lean must refuse the inexact image`)
  const rounded = Number(magnitude)
  assert.notEqual(BigInt(rounded), magnitude)
  assert.equal(Schema.decodeUnknownSync(numberCodec)(Schema.encodeSync(numberCodec)(rounded)), rounded)
  encodingRefusalNames.push(name)
  boundaryDifferences++
}
assert.deepEqual(Object.keys(encodingRefusals).sort(), encodingRefusalNames.sort(), "uncompared or missing Lean encoding refusal")
// Datum transport retains -0; ordinary JSON text deliberately does not.
assert.equal(encoded.numberNegativeZero, -0)
assert.equal(JSON.stringify(encoded.numberNegativeZero), "0")
assert.equal(JSON.parse(JSON.stringify(encoded.numberNegativeZero)), 0)
boundaryDifferences++

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
negativeControls++
assert.throws(() => Schema.decodeUnknownSync(Schema.toCodecJson(
  Schema.Cause(Schema.String, Schema.Defect())))({ reasons: [] }))
negativeControls++
console.log(`PASS schema-codec: ${checked} fresh Lean/rc.112 comparisons, ${checked} host round trips, ${numericNames.length} host encodings observed by Lean decoders, ${matchingRefusals} matching decoder refusals, ${matchingEncoderRefusals} matching encoder refusals, ${negativeControls} negative controls, ${boundaryDifferences} explicit boundary differences`)
