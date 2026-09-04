/**
 * PROBE 1 — canonical emission order (obligation SC-DOC-07).
 *
 * Executes effect@4.0.0-rc.112. Every line printed below is an OBSERVATION
 * of the pinned runtime, not a prediction.
 *
 * Questions:
 *   1a  is emitted union member order source order, or normalised?
 *   1b  is emitted object property order source order, or normalised?
 *   1c  is the references-table key order insertion order, sorted, or other?
 *   1d  are two structurally identical schemas built by different routes
 *       byte-identical after JSON.stringify?
 *   1e  does Effect's own JSON round trip preserve the bytes?
 */
import { Schema, SchemaRepresentation } from "effect"

const out = (label: string, value: unknown): void => {
  console.log(`--- ${label}`)
  console.log(typeof value === "string" ? value : JSON.stringify(value))
}

const bytes = (schema: Schema.Top): string =>
  JSON.stringify(
    SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(schema.ast)),
  )

const doc = (schema: Schema.Top): any =>
  SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(schema.ast))

console.log(`runtime effect@${
  (await import("effect/package.json", { with: { type: "json" } })).default.version
}`)

/* ------------------------------------------------------------------ 1a */
// Union member order, two source arrangements of the same member SET.
const U1 = Schema.Union([Schema.String, Schema.Number, Schema.Boolean])
const U2 = Schema.Union([Schema.Boolean, Schema.Number, Schema.String])
out("1a.union-source-order-A [String, Number, Boolean]", bytes(U1))
out("1a.union-source-order-B [Boolean, Number, String]", bytes(U2))
out("1a.A-bytes-equal-B", bytes(U1) === bytes(U2))

// Does the toCodecJson reorder (BigInt/Symbol/UniqueSymbol first) show up
// in the EMITTED representation of a user union?
const U3 = Schema.Union([Schema.String, Schema.BigInt, Schema.Number])
out("1a.union-with-BigInt-in-middle", bytes(U3))
out(
  "1a.union-with-BigInt member tags in emission order",
  (doc(U3).representation.types as Array<any>).map((t) => t._tag),
)

// oneOf vs anyOf mode spelling.
const U4 = Schema.Union([Schema.String, Schema.Number], { mode: "oneOf" })
out("1a.union-oneOf", bytes(U4))

/* ------------------------------------------------------------------ 1b */
const S1 = Schema.Struct({ b: Schema.String, a: Schema.Number })
const S2 = Schema.Struct({ a: Schema.Number, b: Schema.String })
out("1b.struct-source-order-{b,a}", bytes(S1))
out("1b.struct-source-order-{a,b}", bytes(S2))
out("1b.struct-A-bytes-equal-B", bytes(S1) === bytes(S2))
out(
  "1b.struct-{b,a} emitted property names",
  (doc(S1).representation.propertySignatures as Array<any>).map((p) => p.name),
)

/* ------------------------------------------------------------------ 1c */
const Zed = Schema.String.annotate({ identifier: "Zed" })
const Alpha = Schema.String.annotate({ identifier: "Alpha" })
const Mid = Schema.String.annotate({ identifier: "Mid" })
const R1 = Schema.Struct({ z: Zed, a: Alpha, m: Mid, z2: Zed })
const R2 = Schema.Struct({ a: Alpha, m: Mid, z: Zed, a2: Alpha })
out("1c.references-keys-source-order-{z,a,m}", Object.keys(doc(R1).references))
out("1c.references-keys-source-order-{a,m,z}", Object.keys(doc(R2).references))
out("1c.references-table-A-bytes", JSON.stringify(doc(R1).references))
out("1c.references-table-B-bytes", JSON.stringify(doc(R2).references))

/* ------------------------------------------------------------------ 1d */
// Same member set, two construction ROUTES.
const RouteA = Schema.NullOr(Schema.String)
const RouteB = Schema.Union([Schema.String, Schema.Null])
out("1d.NullOr(String)", bytes(RouteA))
out("1d.Union([String, Null])", bytes(RouteB))
out("1d.NullOr-equals-Union", bytes(RouteA) === bytes(RouteB))

const LitsA = Schema.Literals(["a", "b"])
const LitsB = Schema.Union([Schema.Literal("a"), Schema.Literal("b")])
out("1d.Literals([a,b])", bytes(LitsA))
out("1d.Union([Literal a, Literal b])", bytes(LitsB))
out("1d.Literals-equals-Union", bytes(LitsA) === bytes(LitsB))

const OptA = Schema.Struct({ x: Schema.optional(Schema.String) })
const OptB = Schema.Struct({ x: Schema.UndefinedOr(Schema.String) })
out("1d.Struct{x: optional(String)}", bytes(OptA))
out("1d.Struct{x: UndefinedOr(String)}", bytes(OptB))
out("1d.optional-equals-UndefinedOr", bytes(OptA) === bytes(OptB))

/* ------------------------------------------------------------------ 1e */
const roundTrip = (schema: Schema.Top): string => {
  const json = doc(schema)
  return JSON.stringify(
    SchemaRepresentation.toJson(SchemaRepresentation.fromJson(json as never)),
  )
}
for (const [name, schema] of [
  ["U1", U1],
  ["U3", U3],
  ["S1", S1],
  ["R1", R1],
] as Array<[string, Schema.Top]>) {
  out(`1e.roundtrip-byte-identical:${name}`, roundTrip(schema) === bytes(schema))
}

// A hand-written references table in DELIBERATELY non-sorted key order:
// does fromJson/toJson preserve the key order verbatim?
const handTable = {
  representation: { _tag: "Reference", $ref: "Zed" },
  references: {
    Zed: { _tag: "String", checks: [] },
    Alpha: { _tag: "Number", checks: [] },
    Mid: { _tag: "Boolean", checks: [] },
  },
}
out("1e.hand-table-in", JSON.stringify(handTable))
out(
  "1e.hand-table-out",
  JSON.stringify(SchemaRepresentation.toJson(SchemaRepresentation.fromJson(handTable as never))),
)

/* ------------------------------------------------------------------ 1f */
// The references table is a JS object. ECMAScript orders integer-index-like
// own keys FIRST and NUMERICALLY, ahead of insertion order. If a reference
// name is integer-like, the emitted table key order is not insertion order.
const numericTable = {
  representation: { _tag: "Reference", $ref: "10" },
  references: {
    Zed: { _tag: "String", checks: [] },
    "10": { _tag: "Number", checks: [] },
    "2": { _tag: "Boolean", checks: [] },
    Alpha: { _tag: "Null", checks: [] },
  },
}
out("1f.numeric-table-in-source-key-order", ["Zed", "10", "2", "Alpha"])
out("1f.numeric-table-in-bytes", JSON.stringify(numericTable))
out(
  "1f.numeric-table-out-bytes",
  JSON.stringify(SchemaRepresentation.toJson(SchemaRepresentation.fromJson(numericTable as never))),
)
out(
  "1f.numeric-table-out-keys",
  Object.keys(
    (SchemaRepresentation.toJson(SchemaRepresentation.fromJson(numericTable as never)) as any)
      .references,
  ),
)

/* ------------------------------------------------------------------ 1g */
// Determinism within one process: same schema, emitted twice.
out("1g.same-schema-twice-identical", bytes(S1) === bytes(S1))
// Two independently constructed but textually identical schemas.
const S3 = Schema.Struct({ b: Schema.String, a: Schema.Number })
out("1g.independently-built-identical-source-identical-bytes", bytes(S1) === bytes(S3))

/* ------------------------------------------------------------------ 1h */
// Two DIFFERENT schemas that both claim identifier "N": does the table
// collide, suffix, or silently keep one?
const N1 = Schema.String.annotate({ identifier: "N" })
const N2 = Schema.Number.annotate({ identifier: "N" })
const Collide = Schema.Struct({ p: N1, q: N2, r: N1, s: N2 })
out("1h.identifier-collision-bytes", bytes(Collide))
out("1h.identifier-collision-table-keys", Object.keys(doc(Collide).references))

/* ------------------------------------------------------------------ 1i */
// Byte-level, from a JSON *string* rather than a JS object literal, so the
// authored key order is the one on the wire.
const authored =
  '{"representation":{"_tag":"Reference","$ref":"Zed"},"references":{"Zed":{"_tag":"String","checks":[]},"10":{"_tag":"Number","checks":[]},"2":{"_tag":"Boolean","checks":[]}}}'
const reemitted = JSON.stringify(
  SchemaRepresentation.toJson(SchemaRepresentation.fromJson(JSON.parse(authored))),
)
out("1i.authored-wire-bytes", authored)
out("1i.reemitted-wire-bytes", reemitted)
out("1i.wire-bytes-identical", authored === reemitted)

// The same input with a DUPLICATE key: what survives JSON.parse?
const dupKeys =
  '{"representation":{"_tag":"String","checks":[]},"references":{"A":{"_tag":"String","checks":[]},"A":{"_tag":"Number","checks":[]}}}'
const dupOut = JSON.stringify(
  SchemaRepresentation.toJson(SchemaRepresentation.fromJson(JSON.parse(dupKeys))),
)
out("1i.duplicate-key-authored", dupKeys)
out("1i.duplicate-key-reemitted", dupOut)

/* ------------------------------------------------------------------ 1j */
// Node-level KEY order: is the key order of a representation node normalised
// by the codec, or echoed from the input?
const scrambled = {
  references: {},
  representation: {
    indexSignatures: [],
    checks: [],
    propertySignatures: [
      { isMutable: false, type: { checks: [], _tag: "String" }, name: { value: "a", type: "string" }, isOptional: false },
    ],
    _tag: "Objects",
  },
}
const scrambledText = JSON.stringify(scrambled)
const normalisedText = JSON.stringify(
  SchemaRepresentation.toJson(SchemaRepresentation.fromJson(JSON.parse(scrambledText))),
)
out("1j.scrambled-node-key-order-in", scrambledText)
out("1j.reemitted", normalisedText)
out("1j.node-key-order-normalised", scrambledText !== normalisedText)
out("1j.reemitted-is-idempotent", JSON.stringify(
  SchemaRepresentation.toJson(SchemaRepresentation.fromJson(JSON.parse(normalisedText))),
) === normalisedText)
