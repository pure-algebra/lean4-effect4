/**
 * PROBE 5 — empty and degenerate shapes.
 *
 * Executes effect@4.0.0-rc.112. Every row is an OBSERVATION.
 *
 * Which degenerate shapes does rc.112 accept, and what do they serialize to?
 * Each row is run in BOTH directions where possible:
 *   BUILD  — construct with the public `Schema` API and emit;
 *   WIRE   — hand-write the JSON document and read it back with `fromJson`.
 */
import { Schema, SchemaRepresentation } from "effect"

const out = (label: string, value: unknown): void => {
  console.log(`--- ${label}`)
  console.log(typeof value === "string" ? value : JSON.stringify(value))
}

const build = (label: string, f: () => Schema.Top): void => {
  try {
    out(`BUILD ${label} :: EMITTED`, JSON.stringify(
      SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(f().ast)),
    ))
  } catch (e) {
    out(`BUILD ${label} :: THREW ${(e as Error).constructor.name}`, String((e as Error).message).split("\n").slice(0, 6).join("\n"))
  }
}

const wire = (label: string, document: unknown, multi = false): void => {
  const text = JSON.stringify(document)
  try {
    const back = multi
      ? SchemaRepresentation.toJsonMultiDocument(SchemaRepresentation.fromJsonMultiDocument(document as never))
      : SchemaRepresentation.toJson(SchemaRepresentation.fromJson(document as never))
    const outText = JSON.stringify(back)
    out(`WIRE  ${label} :: ACCEPTED`, outText)
    out(`WIRE  ${label} :: bytes identical`, outText === text)
  } catch (e) {
    out(`WIRE  ${label} :: THREW ${(e as Error).constructor.name}`, String((e as Error).message).split("\n").slice(0, 6).join("\n"))
  }
}

console.log(`runtime effect@${
  (await import("effect/package.json", { with: { type: "json" } })).default.version
}`)

const kw = (t: string) => ({ _tag: t, checks: [] })
const doc = (rep: unknown, refs: unknown = {}) => ({ representation: rep, references: refs })

/* ------------------------------------------------------------- empty union */
build("Schema.Union([])", () => Schema.Union([]))
wire("Union with types: [] and mode anyOf", doc({ _tag: "Union", checks: [], types: [], mode: "anyOf" }))
wire("Union with types: [] and mode oneOf", doc({ _tag: "Union", checks: [], types: [], mode: "oneOf" }))
wire("Union with a bogus mode", doc({ _tag: "Union", checks: [], types: [], mode: "allOf" }))
wire("Union with no mode key", doc({ _tag: "Union", checks: [], types: [] }))

/* ------------------------------------------------------------ empty object */
build("Schema.Struct({})", () => Schema.Struct({}))
wire("Objects with both collections empty",
  doc({ _tag: "Objects", checks: [], propertySignatures: [], indexSignatures: [] }))
wire("Objects with DUPLICATE property keys",
  doc({
    _tag: "Objects", checks: [], indexSignatures: [],
    propertySignatures: [
      { name: { type: "string", value: "a" }, type: kw("String"), isOptional: false, isMutable: false },
      { name: { type: "string", value: "a" }, type: kw("Number"), isOptional: false, isMutable: false },
    ],
  }))

/* ------------------------------------------------------------- empty tuple */
build("Schema.Tuple([])", () => Schema.Tuple([]))
wire("Arrays with elements: [] and rest: []",
  doc({ _tag: "Arrays", checks: [], elements: [], rest: [] }))
wire("Arrays with an optional element BEFORE a required one (E4-SCHEMA-CE-004 shape)",
  doc({
    _tag: "Arrays", checks: [], rest: [],
    elements: [
      { isOptional: true, type: kw("String") },
      { isOptional: false, type: kw("Number") },
    ],
  }))

/* -------------------------------------------------------------- empty enum */
build("Schema.Enum({})", () => Schema.Enum({} as any))
wire("Enum with enums: []", doc({ _tag: "Enum", checks: [], enums: [] }))
wire("Enum with ALIASES (two names, one value) — E4-SCHEMA-CE-003 shape",
  doc({
    _tag: "Enum", checks: [],
    enums: [["A", { type: "number", value: 1 }], ["B", { type: "number", value: 1 }]],
  }))
wire("Enum with a DUPLICATE name",
  doc({
    _tag: "Enum", checks: [],
    enums: [["A", { type: "number", value: 1 }], ["A", { type: "number", value: 2 }]],
  }))

/* --------------------------------------------------- empty template literal */
wire("TemplateLiteral with parts: []", doc({ _tag: "TemplateLiteral", checks: [], parts: [] }))

/* ----------------------------------------------------- empty/odd references */
wire("empty references table (control)", doc(kw("String"), {}))
wire("references table with an EMPTY-STRING key, unreferenced",
  doc(kw("String"), { "": kw("Number") }))
wire("Reference with an EMPTY $ref", doc({ _tag: "Reference", $ref: "" }, { "": kw("Number") }))
wire("references table entry that is itself an empty Union",
  doc({ _tag: "Reference", $ref: "E" }, { E: { _tag: "Union", checks: [], types: [], mode: "anyOf" } }))

/* -------------------------------------------------------- zero-member group */
wire("FilterGroup with checks: [] (zero members)",
  doc({ _tag: "String", checks: [{ _tag: "FilterGroup", checks: [] }] }))
wire("FilterGroup with exactly one check (control)",
  doc({
    _tag: "String",
    checks: [{ _tag: "FilterGroup", checks: [{ _tag: "Filter", representation: { id: "x", payload: null }, aborted: false }] }],
  }))
wire("FilterGroup nested inside a FilterGroup",
  doc({
    _tag: "String",
    checks: [{
      _tag: "FilterGroup",
      checks: [{ _tag: "FilterGroup", checks: [{ _tag: "Filter", representation: { id: "x", payload: null }, aborted: false }] }],
    }],
  }))
wire("Filter WITHOUT a representation (required by the codec)",
  doc({ _tag: "String", checks: [{ _tag: "Filter", aborted: false }] }))

/* ----------------------------------------------------------- empty literals */
build("Schema.Literal(\"\")", () => Schema.Literal(""))
wire("Literal with an empty string value",
  doc({ _tag: "Literal", checks: [], literal: { type: "string", value: "" } }))

/* --------------------------------------------------------- multi-documents */
wire("MultiDocument with representations: [] (empty root list)",
  { representations: [], references: {} }, true)
wire("MultiDocument with one root", { representations: [kw("String")], references: {} }, true)
wire("MultiDocument with three roots",
  { representations: [kw("String"), kw("Number"), kw("Boolean")], references: {} }, true)
wire("MultiDocument shape fed to the SINGLE-document decoder",
  { representations: [kw("String")], references: {} })
wire("Document shape fed to the MULTI-document decoder", doc(kw("String")), true)

/* --------------------------------------------------------------- envelopes */
wire("document with NO references key at all", { representation: kw("String") })
wire("document with an EXCESS key", { representation: kw("String"), references: {}, extra: 1 })
wire("document that is just a bare representation", kw("String"))

/* ---------------------------------------------------- excess-property policy */
wire("representation NODE with an excess key",
  doc({ _tag: "String", checks: [], bogus: 1 }))
wire("property signature with an excess key",
  doc({
    _tag: "Objects", checks: [], indexSignatures: [],
    propertySignatures: [{ name: { type: "string", value: "a" }, type: kw("String"), isOptional: false, isMutable: false, bogus: 1 }],
  }))
wire("index signature with an excess key",
  doc({ _tag: "Objects", checks: [], propertySignatures: [], indexSignatures: [{ parameter: kw("String"), type: kw("Number"), bogus: 1 }] }))
wire("Reference with an excess key", doc({ _tag: "Reference", $ref: "A", checks: [] }, { A: kw("String") }))
wire("Suspend with an excess key", doc({ _tag: "Suspend", checks: [], thunk: kw("String"), bogus: 1 }))
wire("unknown _tag", doc({ _tag: "Import", checks: [] }))
wire("lower-case tag spelling", doc({ _tag: "string", checks: [] }))
wire("keyword node with NO checks key", doc({ _tag: "String" }))

/* -------------------------------------- Suspend/Declaration/Filter minima */
wire("Suspend carrying a check (checks is Schema.Tuple([]))",
  doc({ _tag: "Suspend", checks: [{ _tag: "Filter", representation: { id: "x", payload: null }, aborted: false }], thunk: kw("String") }))
wire("Suspend with checks: [] (control)", doc({ _tag: "Suspend", checks: [], thunk: kw("String") }))
wire("Declaration WITHOUT representation (required by the codec)",
  doc({ _tag: "Declaration", typeParameters: [], checks: [] }))
wire("Declaration WITH representation (control)",
  doc({ _tag: "Declaration", representation: { id: "probe/decl", payload: null }, typeParameters: [], checks: [] }))
