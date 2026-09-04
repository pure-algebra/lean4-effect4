/**
 * PROBE 6 — the load-bearing vectors, emitted as machine-readable JSON.
 *
 * Executes effect@4.0.0-rc.112. Prints one JSON object on stdout. Every
 * `observed` field is a captured runtime value, not a prediction.
 */
import { Schema, SchemaRepresentation } from "effect"

const toJson = (d: unknown) => SchemaRepresentation.toJson(d as never)
const fromJson = (j: unknown) => SchemaRepresentation.fromJson(j as never)
const emit = (s: Schema.Top) =>
  JSON.stringify(SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(s.ast)))
const rt = (text: string): string => {
  try {
    return JSON.stringify(toJson(fromJson(JSON.parse(text))))
  } catch (e) {
    return `THREW ${(e as Error).constructor.name}: ${String((e as Error).message).split("\n")[0]}`
  }
}

const kw = (t: string) => ({ _tag: t, checks: [] })

const A = emit(Schema.Union([Schema.String, Schema.Number, Schema.Boolean]))
const B = emit(Schema.Union([Schema.Boolean, Schema.Number, Schema.String]))
const SA = emit(Schema.Struct({ b: Schema.String, a: Schema.Number }))
const SB = emit(Schema.Struct({ a: Schema.Number, b: Schema.String }))

const authoredTable =
  '{"representation":{"_tag":"Reference","$ref":"Zed"},"references":{"Zed":{"_tag":"String","checks":[]},"10":{"_tag":"Number","checks":[]},"2":{"_tag":"Boolean","checks":[]}}}'

const enumNaN = { representation: { _tag: "Enum", checks: [], enums: [["NOT_A_NUMBER", { type: "number", value: "NaN" }]] }, references: {} }
// keys written in the codec's own field order, so the byte comparison below
// measures value survival and not key-order normalisation
const propNaN = {
  representation: {
    _tag: "Objects", checks: [],
    propertySignatures: [{ name: { type: "number", value: "NaN" }, type: kw("String"), isOptional: false, isMutable: false }],
    indexSignatures: [],
  },
  references: {},
}
const litNaN = { representation: { _tag: "Literal", checks: [], literal: { type: "number", value: "NaN" } }, references: {} }

const annotationEmit = (bag: Record<string, unknown>): string =>
  JSON.stringify(SchemaRepresentation.toJson(
    SchemaRepresentation.toRepresentation(Schema.String.annotate(bag as never).ast),
  ))

const vectors = {
  runtime: {
    package: "effect",
    version: (await import("effect/package.json", { with: { type: "json" } })).default.version,
    execution: "Bun direct TypeScript; no independent typecheck",
    sourceDigest: {
      "src/SchemaRepresentation.ts": "a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc",
      "src/Schema.ts": "9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784",
    },
    note: "the fail-closed runner gates the complete retained source/dist closure before execution",
  },

  "SC-DOC-07.union-member-order-is-source-order": {
    question: "is emitted union member order canonical, or the source arrangement?",
    inputA: "Schema.Union([Schema.String, Schema.Number, Schema.Boolean])",
    inputB: "Schema.Union([Schema.Boolean, Schema.Number, Schema.String])",
    observedA: A,
    observedB: B,
    observedBytesEqual: A === B,
    verdict: "member order is the SOURCE order; the same member SET emits different bytes",
  },

  "SC-DOC-07.object-property-order-is-source-order": {
    inputA: "Schema.Struct({ b: String, a: Number })",
    inputB: "Schema.Struct({ a: Number, b: String })",
    observedA: SA,
    observedB: SB,
    observedBytesEqual: SA === SB,
    verdict: "propertySignatures order is the SOURCE order",
  },

  "SC-DOC-07.node-key-order-IS-normalised": {
    question: "is the KEY order inside one representation node normalised?",
    input: '{"references":{},"representation":{"indexSignatures":[],"checks":[],"propertySignatures":[],"_tag":"Objects"}}',
    observed: rt('{"references":{},"representation":{"indexSignatures":[],"checks":[],"propertySignatures":[],"_tag":"Objects"}}'),
    verdict: "YES — node key order follows the codec struct field order, not the input",
  },

  "SC-DOC-07.references-table-key-order-is-NOT-canonical": {
    question: "does the references table preserve authored key order?",
    inputWireText: authoredTable,
    observedWireText: rt(authoredTable),
    observedBytesEqual: rt(authoredTable) === authoredTable,
    verdict:
      "NO — the table is a JS object, so integer-like keys sort numerically ahead of insertion order. encode(decode(bytes)) != bytes.",
  },

  "E4-SCHEMA-CE-012.duplicate-references-key-silently-collapses": {
    inputWireText: '{"representation":{"_tag":"String","checks":[]},"references":{"A":{"_tag":"String","checks":[]},"A":{"_tag":"Number","checks":[]}}}',
    observedWireText: rt('{"representation":{"_tag":"String","checks":[]},"references":{"A":{"_tag":"String","checks":[]},"A":{"_tag":"Number","checks":[]}}}'),
    verdict: "last duplicate wins, silently, at JSON.parse — before Effect sees the value",
  },

  "E4-SCHEMA-CE-023.literal-number-leg-refuses-non-finite": {
    buildAttempt: "Schema.Literal(NaN)",
    observedBuild: (() => { try { Schema.Literal(NaN as never); return "ACCEPTED" } catch (e) { return `THREW ${(e as Error).constructor.name}: ${(e as Error).message}` } })(),
    wireAttemptLiveNaN: JSON.stringify({ literal: { type: "number", value: "<live NaN>" } }),
    observedWireLiveNaN: (() => { try { fromJson({ representation: { _tag: "Literal", checks: [], literal: { type: "number", value: NaN } }, references: {} }); return "ACCEPTED" } catch (e) { return `THREW ${(e as Error).constructor.name}: ${String((e as Error).message).split("\n").join(" | ")}` } })(),
    wireAttemptStringNaN: JSON.stringify(litNaN),
    observedWireStringNaN: rt(JSON.stringify(litNaN)),
    verdict: "the Literal number leg is Finite; NaN is refused at BUILD and at the WIRE, and the string escape hatch is NOT accepted there",
  },

  "E4-SCHEMA-CE-023.enum-value-DOES-carry-non-finite": {
    inputWireText: JSON.stringify(enumNaN),
    observedWireText: rt(JSON.stringify(enumNaN)),
    observedBytesEqual: rt(JSON.stringify(enumNaN)) === JSON.stringify(enumNaN),
    observedDecodedTypeof: typeof (fromJson(enumNaN) as any).representation.enums[0][1],
    observedDecodedIsNaN: globalThis.Number.isNaN((fromJson(enumNaN) as any).representation.enums[0][1]),
    acceptedNonFiniteSpellings: ["Infinity", "-Infinity", "NaN"],
    rejectedSpellingsProbed: ["+Infinity", "nan", "INFINITY", "1.5", "", "1e999", null],
    verdict:
      "YES — a non-finite number reaches a persisted enum value, encoded as one of exactly three tagged STRINGS under type \"number\". `Schema.Json` does not block it.",
  },

  "E4-SCHEMA-CE-023.property-key-DOES-carry-non-finite": {
    inputWireText: JSON.stringify(propNaN),
    observedWireText: rt(JSON.stringify(propNaN)),
    observedBytesEqual: rt(JSON.stringify(propNaN)) === JSON.stringify(propNaN),
    observedDecodedIsNaN: globalThis.Number.isNaN((fromJson(propNaN) as any).representation.propertySignatures[0].name),
    verdict: "YES — a persisted property key can be NaN, via the same three-string escape",
  },

  "E4-SCHEMA-CE-023.third-numeric-domain-check-payload": {
    attempt: "Schema.Number.check(Schema.isBetween({ minimum: 1, maximum: Infinity }))",
    observed: (() => {
      try {
        SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(
          Schema.Number.check(Schema.isBetween({ minimum: 1, maximum: Infinity })).ast,
        ))
        return "ACCEPTED"
      } catch (e) { return `THREW ${(e as Error).constructor.name}: ${(e as Error).message}` }
    })(),
    verdict:
      "a THIRD numeric domain the ruling does not name: a check payload number must be finite, enforced by a host RangeError, not a SchemaError",
  },

  "E4-SCHEMA-CE-023.negative-zero-does-not-survive-JSON-text": {
    observedLivePreservesNegativeZero: globalThis.Object.is(
      (fromJson({ representation: { _tag: "Enum", checks: [], enums: [["Z", { type: "number", value: -0 }]] }, references: {} }) as any)
        .representation.enums[0][1],
      -0,
    ),
    observedWireText: JSON.stringify(toJson(fromJson({ representation: { _tag: "Enum", checks: [], enums: [["Z", { type: "number", value: -0 }]] }, references: {} }))),
    verdict: "-0 survives the live document but JSON.stringify writes 0, so the sign is lost at the byte face",
  },

  "E4-SCHEMA-CE-011.annotation-pruning": {
    control: annotationEmit({ keep: "yes" }),
    functionValue: annotationEmit({ drop: () => 1 }),
    mixed: annotationEmit({ keep: "yes", drop: () => 1 }),
    allNonJson: annotationEmit({ dropA: () => 1, dropB: 1n }),
    emptyBag: annotationEmit({}),
    nestedBadLeaf: annotationEmit({ nested: { good: 1, bad: () => 1 } }),
    nestedNaN: annotationEmit({ nested: { good: 1, bad: NaN } }),
    nullPrototypeObject: annotationEmit({ np: Object.assign(Object.create(null), { a: 1 }) }),
    verdict:
      "pruning is per-ENTRY and whole-tree: one non-JSON leaf drops the whole entry, silently, with no issue; when nothing survives the `annotations` key is omitted, never emitted as {}",
  },

  "E4-SCHEMA-CE-010.local-symbol-fails-at-lowering-not-at-build": {
    observedBuild: (() => { try { const s = Schema.UniqueSymbol(globalThis.Symbol("local")); return `BUILT, ast._tag=${(s as any).ast._tag}` } catch (e) { return `THREW ${(e as Error).constructor.name}` } })(),
    observedEmit: (() => { try { emit(Schema.UniqueSymbol(globalThis.Symbol("local"))); return "ACCEPTED" } catch (e) { return `THREW ${(e as Error).constructor.name}: ${String((e as Error).message).split("\n")[0]}` } })(),
    observedGlobalSymbolEmit: emit(Schema.UniqueSymbol(globalThis.Symbol.for("effect4/probe"))),
    verdict: "a local symbol builds a live schema and fails only at lowering; the refusal is a SchemaError, not a type error",
  },

  "degenerate.verdicts": {
    "Schema.Union([]) emits": emit(Schema.Union([])),
    "Schema.Struct({}) emits": emit(Schema.Struct({})),
    "Schema.Tuple([]) emits": emit(Schema.Tuple([])),
    "Schema.Enum({}) emits": emit(Schema.Enum({} as any)),
    "zero-member FilterGroup": rt(JSON.stringify({ representation: { _tag: "String", checks: [{ _tag: "FilterGroup", checks: [] }] }, references: {} })),
    "Suspend carrying a check": rt(JSON.stringify({ representation: { _tag: "Suspend", checks: [{ _tag: "Filter", representation: { id: "x", payload: null }, aborted: false }], thunk: kw("String") }, references: {} })),
    "Declaration without representation": rt(JSON.stringify({ representation: { _tag: "Declaration", typeParameters: [], checks: [] }, references: {} })),
    "Filter without representation": rt(JSON.stringify({ representation: { _tag: "String", checks: [{ _tag: "Filter", aborted: false }] }, references: {} })),
    "MultiDocument with empty root list": (() => { try { return JSON.stringify(SchemaRepresentation.toJsonMultiDocument(SchemaRepresentation.fromJsonMultiDocument({ representations: [], references: {} } as never))) } catch (e) { return `THREW ${(e as Error).constructor.name}: ${String((e as Error).message).split("\n")[0]}` } })(),
    "empty-string references-table key, unreferenced": rt(JSON.stringify({ representation: kw("String"), references: { "": kw("Number") } })),
    "empty $ref": rt(JSON.stringify({ representation: { _tag: "Reference", $ref: "" }, references: { "": kw("Number") } })),
    "excess key on the document envelope": rt(JSON.stringify({ representation: kw("String"), references: {}, extra: 1 })),
    "excess key on a representation node": rt(JSON.stringify({ representation: { _tag: "String", checks: [], bogus: 1 }, references: {} })),
    verdict:
      "empty union / object / tuple / enum / template-literal parts / references table are all ACCEPTED and emit an empty collection; a zero-member FilterGroup, an empty $ref, a Suspend with a check, a Declaration or Filter without `representation`, and an empty MultiDocument root list are all REFUSED; excess keys are dropped silently",
  },
}

console.log(JSON.stringify(vectors, null, 2))
