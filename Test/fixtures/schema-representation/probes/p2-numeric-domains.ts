/**
 * PROBE 2 — the numeric-domain question (E4-SCHEMA-CE-023).
 *
 * Executes effect@4.0.0-rc.112. Every line is an OBSERVATION.
 *
 * The ruling says: the `Literal` number leg is `Schema.Finite`, while `Enum`
 * values and property-name keys are `Schema.Number`. So a non-finite number
 * is a legal enum value and a legal property key, and not a legal literal.
 *
 * The claim under test is the SECOND-ORDER one: documents encode through
 * `Schema.Json`, which "has no NaN", so the wire may reject a non-finite
 * number that the type admits. This probe records what actually happens.
 */
import { Schema, SchemaRepresentation } from "effect"

const out = (label: string, value: unknown): void => {
  console.log(`--- ${label}`)
  console.log(typeof value === "string" ? value : JSON.stringify(value))
}

const attempt = (label: string, f: () => unknown): void => {
  try {
    const v = f()
    out(`${label} :: RETURNED`, v)
    out(`${label} :: JSON.stringify`, JSON.stringify(v))
  } catch (e) {
    out(`${label} :: THREW ${(e as Error).constructor.name}`, String((e as Error).message).split("\n").slice(0, 12).join("\n"))
  }
}

const toJson = (d: unknown) => SchemaRepresentation.toJson(d as never)
const fromJson = (j: unknown) => SchemaRepresentation.fromJson(j as never)

const kw = (tag: string) => ({ _tag: tag, checks: [] as Array<never> })

/* ============================================================ 2a  Literal */
// Building the schema first: does Schema.Literal even accept NaN?
attempt("2a.Schema.Literal(NaN).ast._tag", () => (Schema.Literal(NaN as never) as any).ast._tag)
attempt("2a.toJson(Schema.Literal(NaN))", () =>
  toJson(SchemaRepresentation.toRepresentation(Schema.Literal(NaN as never).ast)))
attempt("2a.toJson(Schema.Literal(Infinity))", () =>
  toJson(SchemaRepresentation.toRepresentation(Schema.Literal(Infinity as never).ast)))
attempt("2a.toJson(Schema.Literal(1.5))  control", () =>
  toJson(SchemaRepresentation.toRepresentation(Schema.Literal(1.5).ast)))

// Hand-built document: a Literal node whose number leg carries NaN.
attempt("2a.fromJson Literal{type:number,value:NaN}", () =>
  fromJson({
    representation: { _tag: "Literal", checks: [], literal: { type: "number", value: NaN } },
    references: {},
  }))
attempt("2a.fromJson Literal{type:number,value:Infinity}", () =>
  fromJson({
    representation: { _tag: "Literal", checks: [], literal: { type: "number", value: Infinity } },
    references: {},
  }))
// The wire spelling the Number leg uses for non-finites (see 2b): does the
// Literal leg accept it?
attempt("2a.fromJson Literal{type:number,value:\"NaN\"}", () =>
  fromJson({
    representation: { _tag: "Literal", checks: [], literal: { type: "number", value: "NaN" } },
    references: {},
  }))

/* ============================================================ 2b  Enum */
// Enum values are Schema.Number. Hand-build a document with a NaN value and
// round trip it through Effect's own codec.
const enumDoc = (value: unknown) => ({
  representation: {
    _tag: "Enum",
    checks: [],
    enums: [["NOT_A_NUMBER", { type: "number", value }]],
  },
  references: {},
})
attempt("2b.fromJson Enum value NaN (live JS NaN)", () => fromJson(enumDoc(NaN)))
attempt("2b.fromJson Enum value \"NaN\" (wire string)", () => fromJson(enumDoc("NaN")))
attempt("2b.fromJson Enum value \"Infinity\" (wire string)", () => fromJson(enumDoc("Infinity")))
attempt("2b.fromJson Enum value \"-Infinity\" (wire string)", () => fromJson(enumDoc("-Infinity")))
attempt("2b.fromJson Enum value 42 (control)", () => fromJson(enumDoc(42)))

// And back out: does a decoded NaN enum value SURVIVE re-encoding, and as what?
attempt("2b.roundtrip Enum \"NaN\" -> live -> json", () => toJson(fromJson(enumDoc("NaN"))))
attempt("2b.roundtrip Enum \"Infinity\" -> live -> json", () => toJson(fromJson(enumDoc("Infinity"))))

// Starting from a LIVE document object holding a real JS NaN, what does
// toJson emit?
attempt("2b.toJson of live Enum holding real NaN", () =>
  toJson({
    representation: {
      _tag: "Enum",
      annotations: undefined,
      checks: [],
      enums: [["NOT_A_NUMBER", NaN]],
    },
    references: {},
  }))
attempt("2b.toJson of live Enum holding real Infinity", () =>
  toJson({
    representation: {
      _tag: "Enum",
      annotations: undefined,
      checks: [],
      enums: [["INF", Infinity]],
    },
    references: {},
  }))
attempt("2b.toJson of live Enum holding 42 (control)", () =>
  toJson({
    representation: { _tag: "Enum", annotations: undefined, checks: [], enums: [["FORTY_TWO", 42]] },
    references: {},
  }))

/* ============================================================ 2c property key */
const propDoc = (name: unknown) => ({
  representation: {
    _tag: "Objects",
    checks: [],
    propertySignatures: [{ name, type: kw("String"), isOptional: false, isMutable: false }],
    indexSignatures: [],
  },
  references: {},
})
attempt("2c.fromJson property key {type:number,value:NaN}", () =>
  fromJson(propDoc({ type: "number", value: NaN })))
attempt("2c.fromJson property key {type:number,value:\"NaN\"}", () =>
  fromJson(propDoc({ type: "number", value: "NaN" })))
attempt("2c.fromJson property key {type:number,value:\"Infinity\"}", () =>
  fromJson(propDoc({ type: "number", value: "Infinity" })))
attempt("2c.fromJson property key {type:number,value:7} (control)", () =>
  fromJson(propDoc({ type: "number", value: 7 })))
attempt("2c.roundtrip property key \"NaN\" -> live -> json", () =>
  toJson(fromJson(propDoc({ type: "number", value: "NaN" }))))
attempt("2c.toJson of live property key holding real NaN", () =>
  toJson({
    representation: {
      _tag: "Objects",
      annotations: undefined,
      checks: [],
      propertySignatures: [
        { name: NaN, type: kw("String"), isOptional: false, isMutable: false, annotations: undefined },
      ],
      indexSignatures: [],
    },
    references: {},
  }))

/* ============================================================ 2d does the wire form survive JSON text? */
const nanEnum = toJson(fromJson(enumDoc("NaN")))
out("2d.JSON.stringify of the NaN-enum document", JSON.stringify(nanEnum))
out(
  "2d.JSON.parse(JSON.stringify(..)) reads back",
  (() => {
    try {
      return JSON.stringify(toJson(fromJson(JSON.parse(JSON.stringify(nanEnum)))))
    } catch (e) {
      return `THREW: ${(e as Error).message}`
    }
  })(),
)
// A raw JS NaN put through JSON.stringify becomes null. Does null read back?
out("2d.JSON.stringify(NaN)", JSON.stringify(NaN))
attempt("2d.fromJson Enum value null", () => fromJson(enumDoc(null)))

/* ============================================================ 2e exact accepted domain */
// Which strings does the persisted Enum `number` leg accept?
for (const v of ["NaN", "Infinity", "-Infinity", "+Infinity", "nan", "INFINITY", "1.5", "", "1e999"]) {
  attempt(`2e.Enum number-leg accepts ${JSON.stringify(v)}`, () => {
    const live: any = fromJson(enumDoc(v))
    const back = toJson(live)
    return {
      liveValue: globalThis.String(live.representation.enums[0][1]),
      liveTypeof: typeof live.representation.enums[0][1],
      reencoded: (back as any).representation.enums[0][1],
    }
  })
}
// A number-tagged NaN vs a string-tagged "NaN": distinguishable on the wire?
attempt("2e.string-tagged \"NaN\" enum value", () =>
  toJson(fromJson({
    representation: { _tag: "Enum", checks: [], enums: [["K", { type: "string", value: "NaN" }]] },
    references: {},
  })))
// -0 : does the sign survive?
attempt("2e.Enum value -0", () => {
  const live: any = fromJson(enumDoc(-0))
  return {
    isNegativeZero: globalThis.Object.is(live.representation.enums[0][1], -0),
    reencoded: (toJson(live) as any).representation.enums[0][1],
    stringified: JSON.stringify(toJson(live)),
  }
})
