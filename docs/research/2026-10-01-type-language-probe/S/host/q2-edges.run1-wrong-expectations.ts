// Seat S, question 2: rc.112's own behaviour at the edges the per-form K2 arms meet.
// Runs under bun against the VENDORED rc.112 source (tsconfig.json maps effect/* to
// vendor/effect-4.0.0-rc.112/src). Every check states its expectation; a mismatch makes the
// process exit 1. The red twin (q2-edges-red.ts) flips one expectation and must exit 1.
import { deepStrictEqual } from "node:assert"
import * as Schema from "effect/Schema"
import * as SR from "effect/SchemaRepresentation"

const RED = (globalThis as any).process?.env?.Q2_RED === "1"
let failures = 0
let passes = 0
function check(id: string, what: string, actual: unknown, expected: unknown) {
  let ok = true
  try { deepStrictEqual(actual, expected) } catch { ok = false }
  if (ok) passes++
  else failures++
  console.log(`${ok ? "ok  " : "FAIL"} ${id} ${what} :: actual=${show(actual)}${ok ? "" : ` expected=${show(expected)}`}`)
}
function show(x: unknown): string {
  return JSON.stringify(x, (_k, v) => (v === undefined ? "<undefined>" : typeof v === "bigint" ? `${v}n` : Number.isNaN(v) ? "NaN" : Object.is(v, -0) ? "-0" : v))
}
type R = { ok: true; value: unknown } | { ok: false; message: string }
function decode(schema: any, input: unknown, options?: any): R {
  try { return { ok: true, value: Schema.decodeUnknownSync(schema, options)(input) } }
  catch (e: any) { return { ok: false, message: String(e?.message ?? e).split("\n")[0] } }
}
const accepted = (r: R) => r.ok
const keysOf = (r: R) => (r.ok ? Reflect.ownKeys(r.value as object) : null)
const repr = (s: any) => SR.toJson(SR.toRepresentation(s.ast)) as any
const props = (s: any) => s.ast.propertySignatures.map((p: any) => p.name)
function dumpRepr(name: string, s: any) { console.log(`REPR ${name} ${JSON.stringify(repr(s))}`) }

// E1. Struct: a permuted object literal is accepted; the output follows declaration order.
const AB = Schema.Struct({ a: Schema.Number, b: Schema.String })
const e1 = decode(AB, { b: "x", a: 1 })
check("E1a", "Struct({a,b}) accepts {b,a}", accepted(e1), true)
check("E1b", "output keys in declaration order", keysOf(e1), RED ? ["b", "a"] : ["a", "b"])
// E2. A struct declared in another order keeps its declaration order in the representation.
const BA = Schema.Struct({ b: Schema.String, a: Schema.Number })
check("E2a", "Struct({b,a}) property order", props(BA), ["b", "a"])
check("E2b", "Struct({a,b}) property order", props(AB), ["a", "b"])
check("E2c", "the two persisted documents differ (order is content in rc.112)", JSON.stringify(repr(AB)) === JSON.stringify(repr(BA)), false)
dumpRepr("struct-ab", AB)

// E3. Extra keys: ignore (default) strips, error refuses, preserve keeps.
const extra = { a: 1, b: "x", c: true }
check("E3a", "default onExcessProperty strips c", decode(AB, extra), { ok: true, value: { a: 1, b: "x" } })
check("E3b", "onExcessProperty: error refuses c", accepted(decode(AB, extra, { onExcessProperty: "error" })), false)
check("E3c", "onExcessProperty: preserve keeps c", decode(AB, extra, { onExcessProperty: "preserve" }), { ok: true, value: { a: 1, b: "x", c: true } })
check("E3d", "a missing key refuses", accepted(decode(AB, { a: 1 })), false)

// E4. optionalKey versus optional on an absent key and on an explicit undefined.
const OK = Schema.Struct({ a: Schema.optionalKey(Schema.Number) })
const OP = Schema.Struct({ a: Schema.optional(Schema.Number) })
check("E4a", "optionalKey: {} accepted", decode(OK, {}), { ok: true, value: {} })
check("E4b", "optionalKey: {a: undefined} refused", accepted(decode(OK, { a: undefined })), false)
check("E4c", "optional: {} accepted", decode(OP, {}), { ok: true, value: {} })
const e4d = decode(OP, { a: undefined })
check("E4d", "optional: {a: undefined} accepted", accepted(e4d), true)
check("E4e", "optional: the explicit undefined stays an own key of the output", e4d.ok ? Object.hasOwn(e4d.value as object, "a") : null, true)
check("E4f", "optionalKey: null refused", accepted(decode(OK, { a: null })), false)
check("E4g", "optional: null refused", accepted(decode(OP, { a: null })), false)
dumpRepr("optionalKey", OK)
dumpRepr("optional", OP)
check("E4h", "optionalKey persists isOptional=true over Number", repr(OK).representation.propertySignatures[0].isOptional === true && repr(OK).representation.propertySignatures[0].type._tag, "Number")
check("E4i", "optional persists isOptional=true over Union[Number, Undefined]", repr(OP).representation.propertySignatures[0].type.types.map((t: any) => t._tag), ["Number", "Undefined"])
// the JSON codec side: an explicit undefined under optional encodes to an object that JSON text drops
const OPJ = Schema.toCodecJson(OP)
const enc = Schema.encodeUnknownSync(OPJ)({ a: undefined })
check("E4j", "toCodecJson(optional) encodes {a: undefined} with the key present", Object.hasOwn(enc as object, "a"), true)
check("E4k", "JSON text of that encoding drops the key", JSON.stringify(enc), "{}")

// E5. mutableKey: persisted flag, decoding unchanged.
const MK = Schema.Struct({ a: Schema.mutableKey(Schema.Number) })
check("E5a", "mutableKey persists isMutable=true", repr(MK).representation.propertySignatures[0].isMutable, true)
check("E5b", "mutableKey decodes as the plain field", decode(MK, { a: 1 }), { ok: true, value: { a: 1 } })
const MOK = Schema.Struct({ a: Schema.optionalKey(Schema.mutableKey(Schema.String)) })
check("E5c", "optionalKey(mutableKey(_)) persists both flags", [repr(MOK).representation.propertySignatures[0].isOptional, repr(MOK).representation.propertySignatures[0].isMutable], [true, true])
const MOK2 = Schema.Struct({ a: Schema.mutableKey(Schema.optionalKey(Schema.String)) })
check("E5d", "mutableKey(optionalKey(_)) persists the same two flags", JSON.stringify(repr(MOK2)) === JSON.stringify(repr(MOK)), true)

// E6. Record(String, Number): key order, duplicates, integer-like keys.
const RN = Schema.Record(Schema.String, Schema.Number)
dumpRepr("record-string-number", RN)
check("E6a", "Record persists one index signature, no properties", [repr(RN).representation.propertySignatures.length, repr(RN).representation.indexSignatures.length], [0, 1])
check("E6b", "Record output keeps input key order", keysOf(decode(RN, { b: 1, a: 2 })), ["b", "a"])
check("E6c", "Record: JSON text with a duplicate key decodes the last occurrence", decode(RN, JSON.parse('{"a":1,"a":2}')), { ok: true, value: { a: 2 } })
check("E6d", "Record: integer-like keys come first in ascending numeric order", keysOf(decode(RN, { b: 3, "10": 1, "9": 2 })), ["9", "10", "b"])
check("E6e", "Record: a wrong value type refuses", accepted(decode(RN, { a: "x" })), false)
check("E6f", "Record: onExcessProperty error does not refuse index keys", accepted(decode(RN, { z: 1 }, { onExcessProperty: "error" })), true)
const RL = Schema.Record(Schema.Literals(["a", "b"]), Schema.Number)
dumpRepr("record-literals", RL)
check("E6g", "Record(Literals) persists required properties, no index signature", [props(RL), repr(RL).representation.indexSignatures.length], [["a", "b"], 0])
check("E6h", "Record(Literals) refuses a missing literal key", accepted(decode(RL, { a: 1 })), false)
const RNum = Schema.Record(Schema.Number, Schema.String)
dumpRepr("record-number-key", RNum)
check("E6i", "Record(Number, _) accepts a numeric-string key", accepted(decode(RNum, { "1": "x" })), true)
check("E6j", "Record(Number, _) on a non-numeric key", accepted(decode(RNum, { a: "x" })), true)

// E7. Unions of tagged structs; anyOf and oneOf.
const A = Schema.TaggedStruct("A", { x: Schema.Number })
const B = Schema.TaggedStruct("B", { y: Schema.String })
const AB_U = Schema.Union([A, B])
dumpRepr("tagged-union", AB_U)
check("E7a", "Union([A,B]) selects B by _tag", decode(AB_U, { _tag: "B", y: "s" }), { ok: true, value: { _tag: "B", y: "s" } })
check("E7b", "Union([A,B]) refuses a mismatched tag/payload", accepted(decode(AB_U, { _tag: "A", y: "s" })), false)
check("E7c", "TaggedStruct persists _tag first, a Literal", [props(A), repr(A).representation.propertySignatures[0].type._tag], [["_tag", "x"], "Literal"])
const TU = AB_U.pipe(Schema.toTaggedUnion("_tag"))
check("E7d", "toTaggedUnion keeps the union's AST (same persisted document)", JSON.stringify(repr(TU)) === JSON.stringify(repr(AB_U)), true)
check("E7e", "toTaggedUnion adds guards by tag", [TU.guards.A({ _tag: "A", x: 1 }), TU.guards.B({ _tag: "A", x: 1 })], [true, false])
const TU2 = Schema.TaggedUnion({ A: { x: Schema.Number }, B: { y: Schema.String } })
check("E7f", "TaggedUnion({A,B}) persists the same document as Union([TaggedStruct...])", JSON.stringify(repr(TU2)) === JSON.stringify(repr(AB_U)), true)
let dupTagThrows = false
try { Schema.Union([A, Schema.TaggedStruct("A", { z: Schema.Boolean })]).pipe(Schema.toTaggedUnion("_tag")) } catch { dupTagThrows = true }
check("E7g", "toTaggedUnion over two members with one tag", dupTagThrows, false)
const OV = Schema.Union([Schema.Struct({ a: Schema.Number }), Schema.Struct({ a: Schema.Number, b: Schema.String })])
check("E7h", "anyOf answers the first member that succeeds (strips b)", decode(OV, { a: 1, b: "x" }), { ok: true, value: { a: 1 } })
const OV1 = Schema.Union([Schema.Struct({ a: Schema.Number }), Schema.Struct({ a: Schema.Number, b: Schema.String })], { mode: "oneOf" })
check("E7i", "oneOf refuses when two members succeed", accepted(decode(OV1, { a: 1, b: "x" })), false)
let variadicThrows = false
try { (Schema.Union as any)(Schema.String, Schema.Number) } catch { variadicThrows = true }
check("E7j", "Schema.Union(a, b) (variadic) throws; the call shape is Union([a, b])", variadicThrows, true)

// E8. Property names: __proto__, a-b, Unicode, constructor, toString, empty, integer-like.
const computed = Schema.Struct({ ["__proto__"]: Schema.Number })
const quotedProto = Schema.Struct({ "__proto__": Schema.Number } as any)
const fromEntries = Schema.Struct(Object.fromEntries([["__proto__", Schema.Number]]))
check("E8a", "computed [\"__proto__\"] key is a property", props(computed), ["__proto__"])
check("E8b", "quoted \"__proto__\": key sets the prototype, no property", props(quotedProto), [])
check("E8c", "Object.fromEntries keeps the property", props(fromEntries), ["__proto__"])
const protoInput = JSON.parse('{"__proto__": 1}')
const e8d = decode(computed, protoInput, { onExcessProperty: "error" })
check("E8d", "computed-key struct decodes an own __proto__ property", e8d.ok ? [Object.hasOwn(e8d.value as object, "__proto__"), (e8d.value as any)["__proto__"]] : e8d, [true, 1])
check("E8e", "quoted-key struct accepts {} (the field is gone)", accepted(decode(quotedProto, {})), true)
dumpRepr("proto-computed", computed)
const hyphen = Schema.Struct({ "a-b": Schema.String })
check("E8f", "quoted a-b key", props(hyphen), ["a-b"])
let bareHyphen = "ok"
try { Function("Schema", "return Schema.Struct({ a-b: Schema.String })")(Schema) } catch (e: any) { bareHyphen = e?.name }
check("E8g", "an unquoted a-b key is a SyntaxError", bareHyphen, "SyntaxError")
const uni = Schema.Struct({ "é": Schema.String, "日本": Schema.Number, "😀": Schema.Boolean })
check("E8h", "Unicode keys are properties in written order", props(uni), ["é", "日本", "😀"])
check("E8i", "Unicode-keyed struct decodes", accepted(decode(uni, { "é": "x", "日本": 1, "😀": true })), true)
const ctor = Schema.Struct({ constructor: Schema.String, toString: Schema.String })
check("E8j", "constructor/toString are ordinary properties", props(ctor), ["constructor", "toString"])
check("E8k", "constructor/toString struct refuses {} (inherited members are not own keys)", accepted(decode(ctor, {})), false)
check("E8l", "constructor/toString struct accepts own string values", accepted(decode(ctor, { constructor: "c", toString: "t" })), true)
const ctorU = Schema.Struct({ constructor: Schema.Unknown })
check("E8m", "Struct({constructor: Unknown}) on {}: is the inherited member read?", decode(ctorU, {}), { ok: false, message: "Missing key" })
const empty = Schema.Struct({ "": Schema.Number })
check("E8n", "the empty name is a property", props(empty), [""])
check("E8o", "the empty-named struct decodes", decode(empty, { "": 1 }), { ok: true, value: { "": 1 } })
const intLike = Schema.Struct({ b: Schema.Number, "10": Schema.Number, "9": Schema.Number, "01": Schema.Number, a: Schema.Number })
check("E8p", "integer-like names lead in numeric order; \"01\" is not integer-like", props(intLike), ["9", "10", "b", "01", "a"])

// E9. Numbers: the checks Bridge.schema writes; Int and Natural; safe-integer edges; -0.
const natByName = Schema.Number.check(Schema.isInt(), Schema.isGreaterThanOrEqualTo(0))
const natChained = Schema.Number.check(Schema.isInt()).check(Schema.isGreaterThanOrEqualTo(0))
dumpRepr("nat-by-name", natByName)
dumpRepr("natural", Schema.Natural)
dumpRepr("int", Schema.Int)
check("E9a", "Number.check(isInt(), isGreaterThanOrEqualTo(0)) persists as Schema.Natural does", JSON.stringify(repr(natByName)) === JSON.stringify(repr(Schema.Natural)), true)
check("E9b", "the chained spelling persists the same document", JSON.stringify(repr(natChained)) === JSON.stringify(repr(Schema.Natural)), true)
check("E9c", "Number.check(isInt()) persists as Schema.Int does", JSON.stringify(repr(Schema.Number.check(Schema.isInt()))) === JSON.stringify(repr(Schema.Int)), true)
check("E9d", "the persisted isInt filter carries an expected annotation", repr(Schema.Int).representation.checks[0].annotations, { expected: "an integer" })
const two53 = 9007199254740992
check("E9e", "isInt refuses 2^53 (safe integers only)", accepted(decode(Schema.Int, two53)), false)
check("E9f", "isInt accepts 2^53 - 1", accepted(decode(Schema.Int, two53 - 1)), true)
check("E9g", "Natural accepts -0, keeping the sign", (() => { const r = decode(Schema.Natural, -0); return r.ok ? Object.is(r.value, -0) : r })(), true)
check("E9h", "Int refuses 1.5, NaN, Infinity and \"42\"", [1.5, NaN, Infinity, "42"].map((x) => accepted(decode(Schema.Int, x))), [false, false, false, false])
check("E9i", "Int accepts -15", decode(Schema.Int, -15), { ok: true, value: -15 })
check("E9j", "Natural refuses -1", accepted(decode(Schema.Natural, -1)), false)
check("E9k", "plain Number admits NaN and 1.5", [NaN, 1.5].map((x) => accepted(decode(Schema.Number, x))), [true, true])
check("E9l", "toCodecJson(Number) writes NaN as the string \"NaN\"", Schema.encodeUnknownSync(Schema.toCodecJson(Schema.Number))(NaN), "NaN")
check("E9m", "toCodecJson(Int) writes -15 as a number", Schema.encodeUnknownSync(Schema.toCodecJson(Schema.Int))(-15), -15)

// E10. Tuple is not Array; literals.
const T1 = Schema.Tuple([Schema.String])
const A1 = Schema.Array(Schema.String)
dumpRepr("tuple1", T1)
dumpRepr("array", A1)
check("E10a", "Tuple([String]) persists one element, no rest", [repr(T1).representation.elements.length, repr(T1).representation.rest.length], [1, 0])
check("E10b", "Array(String) persists no element, one rest", [repr(A1).representation.elements.length, repr(A1).representation.rest.length], [0, 1])
check("E10c", "the tuple refuses [], the array accepts it", [accepted(decode(T1, [])), accepted(decode(A1, []))], [false, true])
const LS = Schema.Literals(["a", "b", "c"])
dumpRepr("literals3", LS)
check("E10d", "Literals([a,b,c]) persists a flat three-member union", repr(LS).representation.types.map((t: any) => t.literal), ["a", "b", "c"])
const nested = Schema.Union([Schema.Literal("a"), Schema.Union([Schema.Literal("b"), Schema.Literal("c")])])
check("E10e", "a nested anyOf union persists nested (no flattening)", repr(nested).representation.types[1]._tag, "Union")
check("E10f", "the nested and flat unions accept the same three literals", ["a", "b", "c", "d"].map((x) => [accepted(decode(nested, x)), accepted(decode(LS, x))]), [[true, true], [true, true], [true, true], [false, false]])

console.log(`SUMMARY passes=${passes} failures=${failures}${RED ? " (red twin: one expectation flipped)" : ""}`)
if (failures > 0) (globalThis as any).process.exit(1)
