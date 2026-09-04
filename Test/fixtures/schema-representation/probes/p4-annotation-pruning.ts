/**
 * PROBE 4 — annotation pruning (reserved row E4-SCHEMA-CE-011).
 *
 * Executes effect@4.0.0-rc.112. Every row is an OBSERVATION.
 *
 * Question: attach a non-JSON annotation value and serialize. What survives,
 * what is dropped SILENTLY, and what raises?
 */
import { Schema, SchemaRepresentation } from "effect"

const out = (label: string, value: unknown): void => {
  console.log(`--- ${label}`)
  console.log(typeof value === "string" ? value : JSON.stringify(value))
}

const emit = (label: string, annotations: Record<string, unknown>): void => {
  try {
    const json: any = SchemaRepresentation.toJson(
      SchemaRepresentation.toRepresentation(Schema.String.annotate(annotations as never).ast),
    )
    const bag = json.representation.annotations
    out(`${label} :: EMITTED`, JSON.stringify(json))
    out(
      `${label} :: annotations key present`,
      Object.prototype.hasOwnProperty.call(json.representation, "annotations"),
    )
    out(`${label} :: surviving annotation keys`, bag === undefined ? null : Object.keys(bag))
  } catch (e) {
    out(`${label} :: THREW ${(e as Error).constructor.name}`, String((e as Error).message).split("\n").slice(0, 8).join("\n"))
  }
}

console.log(`runtime effect@${
  (await import("effect/package.json", { with: { type: "json" } })).default.version
}`)

/* ---------------------------------------------------- 4a one value at a time */
emit("4a.string  (control)", { probeString: "kept" })
emit("4a.number  (control)", { probeNumber: 1.5 })
emit("4a.boolean (control)", { probeBoolean: true })
emit("4a.null    (control)", { probeNull: null })
emit("4a.array   (control)", { probeArray: [1, "a", null, { b: true }] })
emit("4a.object  (control)", { probeObject: { a: 1, b: [2] } })

emit("4a.function", { probeFunction: () => 1 })
emit("4a.symbol", { probeSymbol: globalThis.Symbol.for("probe/sym") })
emit("4a.local symbol", { probeLocalSymbol: globalThis.Symbol("probe-local") })
emit("4a.Date", { probeDate: new Date(0) })
emit("4a.BigInt", { probeBigInt: 1n })
emit("4a.undefined", { probeUndefined: undefined })
emit("4a.NaN", { probeNaN: NaN })
emit("4a.Infinity", { probeInfinity: Infinity })
emit("4a.-0", { probeNegZero: -0 })
emit("4a.Map", { probeMap: new Map([["a", 1]]) })
emit("4a.Set", { probeSet: new Set([1]) })
emit("4a.RegExp", { probeRegExp: /x/g })
emit("4a.Error", { probeError: new Error("boom") })
emit("4a.class instance", { probeClass: new (class Foo { x = 1 })() })
emit("4a.Object.create(null)", { probeNullProto: Object.assign(Object.create(null), { a: 1 }) })
emit("4a.Uint8Array", { probeBytes: new Uint8Array([1, 2, 3]) })

/* ---------------------------------------------------- 4b nesting */
// Is pruning per-ENTRY or per-LEAF? A JSON-shaped object with ONE bad leaf.
emit("4b.object with a nested function", { probeNested: { good: 1, bad: () => 1 } })
emit("4b.object with a nested NaN", { probeNestedNaN: { good: 1, bad: NaN } })
emit("4b.array with a nested undefined", { probeNestedUndef: [1, undefined, 3] })
// Cyclic value.
const cyc: any = { a: 1 }
cyc.self = cyc
emit("4b.cyclic object", { probeCyclic: cyc })
// A DAG (shared, not cyclic).
const shared = { s: 1 }
emit("4b.shared sub-object (DAG, not a cycle)", { probeDag: { l: shared, r: shared } })

/* ---------------------------------------------------- 4c mixed bag */
emit("4c.mixed: one good, one bad", { keepMe: "yes", dropMe: () => 1 })
emit("4c.all bad -> is the whole `annotations` key omitted?", { dropA: () => 1, dropB: 1n })
emit("4c.empty bag", {})

/* ---------------------------------------------------- 4d key order */
emit("4d.key order z,a,m", { z: 1, a: 2, m: 3 })
emit("4d.key order a,m,z", { a: 2, m: 3, z: 1 })
emit("4d.integer-like keys 10,2,zed", { "10": 1, "2": 2, zed: 3 })

/* ---------------------------------------------------- 4e representation payload */
// `RepresentationAnnotation.payload` is `Schema.Json` — NOT pruned, so a
// non-JSON payload should be an ERROR rather than a silent drop.
const declDoc = (payload: unknown) => ({
  representation: {
    _tag: "Declaration",
    representation: { id: "probe/decl", payload },
    typeParameters: [],
    checks: [],
  },
  references: {},
})
for (const [label, payload] of [
  ["null (control)", null],
  ["{a:1} (control)", { a: 1 }],
  ["NaN", NaN],
  ["Infinity", Infinity],
  ["undefined", undefined],
  ["a function", () => 1],
  ["a Date", new Date(0)],
] as Array<[string, unknown]>) {
  try {
    const back = SchemaRepresentation.toJson(SchemaRepresentation.fromJson(declDoc(payload) as never))
    out(`4e.Declaration representation.payload = ${label} :: ACCEPTED`, JSON.stringify(back))
  } catch (e) {
    out(
      `4e.Declaration representation.payload = ${label} :: THREW ${(e as Error).constructor.name}`,
      String((e as Error).message).split("\n").slice(0, 4).join("\n"),
    )
  }
}

/* ---------------------------------------------------- 4f empty id */
for (const [label, id] of [["empty string", ""], ["ok", "probe/decl"]] as Array<[string, string]>) {
  try {
    const back = SchemaRepresentation.toJson(
      SchemaRepresentation.fromJson({
        representation: { _tag: "Declaration", representation: { id, payload: null }, typeParameters: [], checks: [] },
        references: {},
      } as never),
    )
    out(`4f.Declaration representation.id = ${label} :: ACCEPTED`, JSON.stringify(back))
  } catch (e) {
    out(
      `4f.Declaration representation.id = ${label} :: THREW ${(e as Error).constructor.name}`,
      String((e as Error).message).split("\n").slice(0, 4).join("\n"),
    )
  }
}
