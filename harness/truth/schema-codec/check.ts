import assert from "node:assert/strict"
import { isDeepStrictEqual } from "node:util"
import { Cause, Exit, Option, Result, Schema, SchemaRepresentation } from "effect"
import effectPackage from "effect/package.json"
// Written fresh by Emit.lean before tsgo checks this file: Lean's codec results, and each case's
// typed Schema as the code printer writes it (`Codegen.SchemaCode.ofTy`). The checker writes no
// Schema by hand: every case's type has generated code since the bridge lowers `number`.
import {
  documents, encodingRefusals, encodingRefusalSchemas, encodings as encoded, numericDecodings, refusals,
  refusalSchemas, schemas, unlowered
} from "./.work/values.ts"

assert.equal(effectPackage.version, "4.0.0-rc.112")

/** A case's generated Schema, the code printer's (`Codegen.SchemaCode.ofTy`). */
function generated(table: Readonly<Record<string, unknown>>, name: string): unknown {
  assert.ok(Object.hasOwn(table, name), `${name}: no generated Schema (${unlowered[name]})`)
  return table[name]
}
assert.deepEqual(unlowered, {}, "every case's type has generated Schema code")

const cause = Cause.fromReasons([
  Cause.makeFailReason("bad"),
  Cause.makeDieReason({ user: 7 }),
  Cause.makeInterruptReason(undefined),
  Cause.makeInterruptReason(9)
])
let checked = 0
const names: string[] = []
function check<S extends Schema.ConstraintCodec<unknown, unknown>>(name: string, schema: S, value: S["Type"]) {
  assert.equal(schema, generated(schemas, name), `${name}: not the case's generated Schema`)
  const codec = Schema.toCodecJson(schema)
  const host = Schema.encodeSync(codec)(value)
  assert.deepEqual(encoded[name], host, `${name}: Lean/rc.112 encoding differs`)
  const recovered = Schema.decodeUnknownSync(codec)(encoded[name])
  assert.deepEqual(Schema.encodeSync(codec)(recovered), host, `${name}: host round trip differs`)
  names.push(name)
  checked++
}

check("unit", schemas.unit, undefined)
check("bool", schemas.bool, true)
check("nat", schemas.nat, 42)
check("string", schemas.string, "λ🙂")
check("literal", schemas.literal, "User")
check("pair", schemas.pair, [3, "x"])
check("list", schemas.list, [true, false])
check("none", schemas.none, Option.none())
check("some", schemas.some, Option.some(7))
check("resultFailure", schemas.resultFailure, Result.fail("bad"))
check("resultSuccess", schemas.resultSuccess, Result.succeed(true))
check("exitSuccess", schemas.exitSuccess, Exit.succeed(true))
check("exitFailure", schemas.exitFailure, Exit.failCause(cause))
check("cause", schemas.cause, cause)
check("emptyCause", schemas.emptyCause, Cause.empty)
check("union", schemas.union, 4)
check("nested", schemas.nested, [Option.some(Result.succeed(true)), Option.none()])
const ada = { name: "Ada" }
const adaNone = { name: "Ada", nickname: Option.none<string>() }
const adaSome = { name: "Ada", nickname: Option.some("A") }
check("recordAbsent", schemas.recordAbsent, ada)
check("recordNone", schemas.recordNone, adaNone)
check("recordSome", schemas.recordSome, adaSome)
check("recordVoidAbsent", schemas.recordVoidAbsent, {})
check("recordVoidPresent", schemas.recordVoidPresent, { slot: undefined })
check("recordKeys", schemas.recordKeys, { "": "empty", ["__proto__"]: 7, "a-b": true })
check("mapEmpty", schemas.mapEmpty, {})
check("mapKeys", schemas.mapKeys, { "2": 2, "10": 10, ["__proto__"]: 7, "a-b": 3, "λ🙂": 4 })
check("mapRecords", schemas.mapRecords, { ["__proto__"]: ada, "a-b": adaNone })
check("tuple0", schemas.tuple0, [])
check("tuple1", schemas.tuple1, [7])
check("tuple2", schemas.tuple2, [7, "x"])
check("tuple3", schemas.tuple3, [7, "x", true])
check("nestedRecordMapTuple", schemas.nestedRecordMapTuple,
  { rows: { ["__proto__"]: [adaSome, Option.some(9), true], "a-b": [ada, Option.none(), false] } })
check("nestedTupleRecordMap", schemas.nestedTupleRecordMap,
  [{ slot: undefined }, { "a-b": Option.none(), ["__proto__"]: Option.some("ok") }, []])

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
function checkNumeric(name: string, value: number) {
  const schema = generated(schemas, name) as typeof Schema.Number
  check(name, schema, value)
  const codec = Schema.toCodecJson(schema)
  const host = Schema.encodeSync(codec)(value)
  validateNumeric(name, numericDecodings, host)
  assert.equal(Schema.decodeUnknownSync(codec)(encoded[name]), value, `${name}: host decoder changed the numeric datum`)
  numericNames.push(name)
}
checkNumeric("intZero", 0)
checkNumeric("intPositive", 404)
checkNumeric("intNegative", -15)
checkNumeric("intPositiveBound", Number.MAX_SAFE_INTEGER)
checkNumeric("intNegativeBound", -Number.MAX_SAFE_INTEGER)
checkNumeric("numberZero", 0)
checkNumeric("numberPositive", 3)
checkNumeric("numberNegative", -3)
checkNumeric("numberPositiveFraction", 0.5)
checkNumeric("numberNegativeFraction", -0.5)
checkNumeric("numberNegativeZero", -0)
checkNumeric("numberPositiveBound", Number.MAX_SAFE_INTEGER)
checkNumeric("numberNegativeBound", -Number.MAX_SAFE_INTEGER)
checkNumeric("numberAboveBound", 2 ** 53)
checkNumeric("numberBelowBound", -(2 ** 53))
checkNumeric("numberLargePositive", 2 ** 60)
checkNumeric("numberLargeNegative", -(2 ** 60))
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
const slotCodec = Schema.toCodecJson(schemas.recordVoidAbsent)
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
/** A refusal case's generated Schema, as a codec's source. */
const refusalSchema = (name: string) => generated(refusalSchemas, name) as Schema.ConstraintCodec<unknown, unknown>
function checkRefusal(name: string) {
  const fixture = refusals[name]
  assert.equal(fixture.refused, true, `${name}: Lean must refuse`)
  // Strict excess-property handling matches this Lean record boundary.
  assert.throws(() => Schema.decodeUnknownSync(Schema.toCodecJson(refusalSchema(name)),
    { onExcessProperty: "error" })(fixture.input), `${name}: rc.112 must refuse`)
  refusalNames.push(name)
  matchingRefusals++
}
for (const name of [
  "recordMissing", "recordExtra", "recordWrong", "mapWrong", "tuple0Long", "tuple1Short", "tuple1Long",
  "tuple3Short", "tuple3Long", "tuple3Wrong", "intAboveBound", "intBelowBound", "intPositiveFraction",
  "intNegativeFraction", "intNaN", "intPositiveInfinity", "intNegativeInfinity", "intWrongType", "numberWrongType"
]) checkRefusal(name)

const encodingRefusalNames: string[] = []
let matchingEncoderRefusals = 0
for (const [name, value] of [
  ["intAboveBound", 2 ** 53],
  ["intBelowBound", -(2 ** 53)],
  ["intPositiveFraction", 0.5],
  ["intNegativeFraction", -0.5],
  ["intNaN", NaN],
  ["intPositiveInfinity", Infinity],
  ["intNegativeInfinity", -Infinity],
  ["intWrongType", "1"],
  ["numberWrongType", "1"]
] as const) {
  assert.equal(encodingRefusals[name], true, `${name}: Lean encoder must refuse`)
  const codec = Schema.toCodecJson(generated(encodingRefusalSchemas, name) as Schema.ConstraintCodec<unknown, unknown>)
  const encodeUnknown = Schema.encodeUnknownSync(codec)
  assert.throws(() => encodeUnknown(value), `${name}: rc.112 encoder must refuse`)
  encodingRefusalNames.push(name)
  matchingEncoderRefusals++
}

// The integer codec excludes -0 even though rc.112's isInt accepts it.
assert.equal(refusals.intNegativeZero.refused, true)
assert.equal(encodingRefusals.intNegativeZero, true)
assert.equal(refusals.intNegativeZero.input, -0)
const intCodec = Schema.toCodecJson(refusalSchema("intNegativeZero") as typeof Schema.Number)
assert.equal(Schema.decodeUnknownSync(intCodec)(refusals.intNegativeZero.input), -0)
assert.equal(Schema.encodeSync(intCodec)(-0), -0)
refusalNames.push("intNegativeZero")
encodingRefusalNames.push("intNegativeZero")
boundaryDifferences++

// NaN and infinities stay outside the Lean number codec. The host writes named strings.
const numberCodec = Schema.toCodecJson(refusalSchema("numberNaN") as typeof Schema.Number)
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
assert.deepEqual(Schema.decodeUnknownSync(Schema.toCodecJson(refusalSchema("recordExtra")))(refusals.recordExtra.input), ada)
// JSON text parsing collapses duplicate keys before Schema sees an object.
// These observations document the boundary difference, not matching raw inputs.
for (const [name, text, expected] of [
  ["recordDuplicate", '{"name":"Ada","name":"Grace"}', { name: "Grace" }],
  ["mapDuplicate", '{"x":1,"x":2}', { x: 2 }]
] as const) {
  assert.equal(refusals[name].refused, true, `${name}: Lean entry-list input must refuse`)
  assert.deepEqual(refusals[name].input, JSON.parse(text), `${name}: host object conversion keeps the last key`)
  assert.deepEqual(Schema.decodeUnknownSync(Schema.toCodecJson(refusalSchema(name)))(JSON.parse(text)), expected)
  refusalNames.push(name)
}
assert.deepEqual(Object.keys(refusals).sort(), refusalNames.sort(), "uncompared or missing Lean refusal")

// Negative controls catch the two incorrect shapes in the original specification.
assert.throws(() => Schema.decodeUnknownSync(Schema.toCodecJson(schemas.resultSuccess))({ _tag: "Success", value: true }))
negativeControls++
assert.throws(() => Schema.decodeUnknownSync(Schema.toCodecJson(schemas.cause))({ reasons: [] }))
negativeControls++

// The generated Schemas are rc.112's reading of Lean's documents (the review's P4, option (a)).
// For each case whose type the printer writes, rc.112 revives Lean's persisted document
// (`Codegen.Schema.documentExpr`) with its own revivers, and the generated Schema has the revived
// Schema's representation. rc.112's code generator (`toCodeDocument`) then writes the revived
// Schema's code, and that code, evaluated, has the representation too: but at a `__proto__` key,
// which rc.112 quotes, so that its object literal sets the prototype and drops the field.
const revivers = [Schema.OptionReviver, Schema.ResultReviver, Schema.ExitReviver, Schema.CauseReviver,
  Schema.JsonReviver, Schema.isIntReviver, Schema.isGreaterThanOrEqualToReviver]
const representationOf = (schema: Schema.Top) =>
  SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(schema.ast))
const revive = (name: string) =>
  SchemaRepresentation.fromRepresentation(SchemaRepresentation.fromJson(documents[name]!), { revivers })
let revived = 0
const codeDifferences: string[] = []
for (const [name, schema] of Object.entries(schemas) as Array<[string, Schema.Top]>) {
  const host = revive(name)
  assert.deepEqual(representationOf(schema), representationOf(host), `${name}: not rc.112's revival of Lean's document`)
  revived++
  const code = SchemaRepresentation.toCodeDocument(
    SchemaRepresentation.toMultiDocument(SchemaRepresentation.toRepresentation(host.ast))).codes[0]!.runtime
  const rebuilt = new Function("Schema", `return (${code})`)(Schema) as Schema.Top
  if (!isDeepStrictEqual(representationOf(rebuilt), representationOf(schema))) codeDifferences.push(name)
}
assert.deepEqual(Object.keys(documents).sort(), Object.keys(schemas).sort(), "a generated Schema without its document")
assert.deepEqual(codeDifferences, ["recordKeys"], "rc.112's code differs only at the quoted __proto__ key")
// A red control: the hand Schema this gate held for `pair` until CR-4 is not rc.112's revival of
// Lean's document, whose first position is a natural, not any number.
assert.throws(() => assert.deepEqual(representationOf(Schema.Tuple([Schema.Number, Schema.String])),
  representationOf(revive("pair"))))
negativeControls++
console.log(`PASS schema-codec: ${checked} fresh Lean/rc.112 comparisons, ${checked} host round trips, ${numericNames.length} host encodings observed by Lean decoders, ${matchingRefusals} matching decoder refusals, ${matchingEncoderRefusals} matching encoder refusals, ${negativeControls} negative controls, ${boundaryDifferences} explicit boundary differences; ${Object.keys(schemas).length} generated Schemas, ${revived} equal to rc.112's revival of their documents, ${revived - codeDifferences.length} to its code of them (${codeDifferences.length} difference, its quoted __proto__ key)`)
