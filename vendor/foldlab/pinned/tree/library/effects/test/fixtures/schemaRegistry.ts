/**
 * The hand-mirrored schema registry: the TypeScript twin of
 * `library/cas/tools/Schemas.lean`, name for name and order for order.
 *
 * The mirrors are written by hand on purpose — they are the drift
 * tripwire against the Lean-emitted fixtures in `library/cas/schemas/`,
 * so nothing here may be derived from those fixtures. Two suites read
 * this registry (the byte pin and the materialization gate), which is why
 * it lives in one place instead of being copied.
 */
import { Schema } from "effect"
import { Cas } from "../../src/index.ts"

const { Annotations, CanonicalSchema, ConformanceVector, Exchanges } = Cas

/** Lean `SchemasMain.PinSample`, hand-mirrored in Effect Schema. */
export const pinSample = Schema.Struct({
  count: Schema.Int,
  flag: Schema.Boolean,
  items: Schema.Array(Schema.String),
  label: Schema.String,
  note: Schema.optionalKey(Schema.String),
  root: CanonicalSchema.ref(9),
  unit: Schema.Null,
})

/** Lean `SchemasMain.literalPin`, hand-mirrored in Effect Schema. */
export const literalPin = Schema.Struct({
  a: Schema.Null,
  b: Schema.Literal(true),
  c: Schema.optionalKey(Schema.Literal(-7)),
  d: Schema.Literal("pinned"),
})

/** Lean `SchemasMain.unionPin`, hand-mirrored in Effect Schema.
 *
 * ORDER IS IDENTITY: `exact` spells `"zebra"` before `"alpha"` on both
 * sides on purpose. Any sort of union members — here or in Lean — moves
 * the payload bytes and the address, and the pin goes red. `nested`
 * mirrors the no-flattening rule: it is a union whose second member is
 * a union, not a three-member union.
 *
 * `choice` and `nested` carry no `mode` option because Effect's own
 * constructor defaults it to `"anyOf"`, which is the mode the Lean code
 * spells; the estate's emitter always writes the mode out, which is a
 * lowering choice and not a representation difference. */
export const unionPin = Schema.Struct({
  choice: Schema.Union([Schema.String, Schema.Boolean, Schema.Int]),
  exact: Schema.Union([Schema.Literal("zebra"), Schema.Literal("alpha")], {
    mode: "oneOf",
  }),
  nested: Schema.optionalKey(Schema.Union([
    Schema.Null,
    Schema.Union([Schema.Array(Schema.String), Schema.Boolean], {
      mode: "oneOf",
    }),
  ])),
})

/** Lean `SchemasMain.TaggedPin`, hand-mirrored in Effect Schema.
 *
 * The Lean side does NOT hand-write this code: it is what
 * `deriving Described` emits for the inductive
 *
 *     inductive TaggedPin
 *       | move (dx : SafeInt) (dy : SafeInt)
 *       | stop
 *       | say (body : String) (note : Option String)
 *
 * so this mirror is the tripwire on the GENERATOR, not on a hand-composed
 * code. Two spellings the generator commits to and this mirror holds:
 *
 * - member order is ASCENDING TAG (`move`, `say`, `stop`), not source
 *   order — order is identity, so a generator has to pick one, and it
 *   picks the one that does not move when the source is shuffled;
 * - the mode is `oneOf`, spelled, because the members are pairwise
 *   disjoint by construction and the estate never elides a mode.
 *
 * `_tag` is Effect's own TaggedStruct discriminant name, first in each
 * member, which is what makes the union discriminated — the property the
 * Lean side proves as `TaggedPin.schemaDiscriminated`. This is written as
 * a plain `Schema.Union` of `Schema.Struct`s rather than
 * `Schema.TaggedUnion` on purpose: `TaggedUnion` builds at Effect's
 * default `anyOf`, and the mode is part of the identity here. */
export const taggedPin = Schema.Union([
  Schema.Struct({
    _tag: Schema.Literal("move"),
    dx: Schema.Int,
    dy: Schema.Int,
  }),
  Schema.Struct({
    _tag: Schema.Literal("say"),
    body: Schema.String,
    note: Schema.optionalKey(Schema.String),
  }),
  Schema.Struct({
    _tag: Schema.Literal("stop"),
  }),
], { mode: "oneOf" })

/** Lean `SchemasMain.enumPin`, hand-mirrored in Effect Schema.
 *
 * ORDER IS IDENTITY here too, and for a reason visible in Effect's own
 * constructor: `Schema.Enum` reads its members as
 * `Object.keys(enums).filter(...).map(key => [key, enums[key]])`, so the
 * persisted order is insertion order — source order for a TypeScript
 * `enum`, literal order for the objects below. `direction` therefore
 * spells `Up` before `Down` on both sides on purpose; any sort moves the
 * payload bytes and the address, and the pin goes red.
 *
 * `level` carries an ALIAS — `Warn` and `Warning` at the same value —
 * which is content TypeScript spells and the Lean `WF` deliberately
 * admits: the member NAME is the identity, the value is not.
 *
 * These are object literals rather than `enum` declarations because a
 * TypeScript `enum` is the one construct that cannot be written in a
 * `.ts` module under `erasableSyntaxOnly`, and because the two build the
 * same `SchemaAST.Enum`: an object literal has no reverse mappings, so
 * the constructor's reverse-mapping filter is a no-op on it. */
export const enumPin = Schema.Struct({
  direction: Schema.Enum({ Up: "Up", Down: "Down" }),
  level: Schema.Enum({ Debug: -1, Warn: 1, Warning: 1 }),
  mixed: Schema.optionalKey(Schema.Enum({ Name: "name", Zero: 0 })),
})

/** Lean `SchemasMain.tuplePin`, hand-mirrored in Effect Schema.
 *
 * Every shape the grown `Arrays` node reaches, beside the plain array
 * whose bytes the Arrays completion must NOT move. `plain` is there for
 * exactly that: `Schema.Array(t)` is `{elements: [], rest: [t]}`, and the
 * Lean carrier cannot spell that as a tuple, so the projection gains no
 * second collapse and this row's bytes are unchanged by the increment.
 *
 * POSITION IS IDENTITY: `pair` spells String before Int on both sides on
 * purpose. `withOptional` carries the optionality bit on a TRAILING
 * element — whether an optional element may sit anywhere else is a
 * denotation question, which the Lean side parks as `tupleEl`, not an
 * admission one. */
export const tuplePin = Schema.Struct({
  nested: Schema.optionalKey(Schema.Tuple([
    Schema.Array(Schema.Tuple([Schema.String])),
    Schema.Null,
  ])),
  pair: Schema.Tuple([Schema.String, Schema.Int]),
  plain: Schema.Array(Schema.String),
  withOptional: Schema.Tuple([Schema.Int, Schema.optionalKey(Schema.String)]),
  withRest: Schema.TupleWithRest(Schema.Tuple([Schema.String]), [Schema.Int]),
})

/** The registry, name-for-name with `library/cas/tools/Schemas.lean`.
 *
 * `annotation` mirrors Lean `Cas.Schema.Annotation` through the library's
 * own hand-written kind rather than a second copy of it: the sidecar
 * annotation kind is a public surface, so the surface itself is what the
 * Lean bytes are held to. It is hand-written like every other row, and
 * like every other row it is never derived from the fixtures.
 *
 * `exchange` mirrors Lean `Cas.Schema.Exchange` the same way, through
 * `Exchanges.Exchange`. Its subject union is the second row after
 * `tagged-pin` whose members the deriving handler spells, so the pin
 * holds the generator's member order and `oneOf` mode inside a struct
 * field — one level deeper than `tagged-pin` reaches. */
export const registry: ReadonlyArray<readonly [string, Schema.Top]> = [
  ["vector-document", ConformanceVector.vectorSchema],
  ["vector-index", ConformanceVector.indexSchema],
  ["pin-sample", pinSample],
  ["literal-pin", literalPin],
  ["annotation", Annotations.Annotation],
  ["union-pin", unionPin],
  ["tagged-pin", taggedPin],
  ["enum-pin", enumPin],
  ["tuple-pin", tuplePin],
  ["exchange", Exchanges.Exchange],
] as const
