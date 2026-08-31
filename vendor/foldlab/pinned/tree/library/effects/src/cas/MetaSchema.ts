/**
 * THE META PLANE'S ONE INTERPRETER: an emitted shape, read as an
 * Effect Schema.
 *
 * ## The law this module keeps
 *
 * THE AST VALUE IS THE SINGLE SOURCE OF TRUTH. A shape exists on the
 * meta plane exactly when `MetaSchema` can spell it; the shapes
 * themselves are TERMS of that type, emitted from
 * `library/cas/tools/MetaShapes.lean` into
 * `generated/meta/metaSchemaAst.META.ts`. This module is the ONE
 * function over them — written once, by hand, exhaustive over the
 * union — so that CONSUMERS NEVER RESTATE THOSE SHAPES BY HAND. A
 * hand-written Effect Schema for an emitted artifact is a second,
 * drifting copy of a document the estate already describes; there is
 * no such copy here, and the point of the cutover is that there is
 * none downstream either.
 *
 * The union is CLOSED, so the switch is exhaustive by construction: a
 * constructor added in Lean lands in the emitted union and makes
 * `absurd`'s argument non-`never`, which is a RED TypeScript build in
 * this file. The compiler is what makes the plane's universe grow by
 * grill rather than by accident.
 *
 * ## Closed records
 *
 * Every `record` decodes CLOSED: an unknown key is a REFUSAL, not a
 * quietly stripped field. That is the same law the emitted JSON
 * Schemas state as `additionalProperties: false`, spelled on this
 * side where Effect v4 keeps it — in `ParseOptions`, at the decode,
 * rather than in the schema value. So `closedDecoding` rides beside
 * the interpreter and `decodeMetaArtifact` is the door that always
 * applies it.
 *
 * ## What is OWED, and deliberately not built here
 *
 * THE AGREEMENT GATE: Effect v4's own derived JSON Schema for
 * `toEffectSchema(shape)`, compared against the Lean-emitted
 * `<stem>.META.schema.json` printed from the same term — two
 * independent printers checking each other, with the Lean printer
 * remaining the committed authority. It is NAMED here and not built:
 * this module is the interpreter, and the agreement is a gate with
 * its own red.
 */
import { absurd, cast, Effect, Option, Schema } from "effect"
import type { SchemaAST } from "effect"
import type { MetaField, MetaSchema } from "./generated/meta/metaSchemaAst.META.ts"
import {
  axiomsShape,
  debtsShape,
  manifestShape,
  namesShape,
  strataShape,
  trustShape,
} from "./generated/meta/metaSchemaAst.META.ts"

export type { MetaField, MetaSchema }

/**
 * What `toEffectSchema` hands back.
 *
 * `unknown` on both sides is not vagueness, it is the honest type: a
 * shape is a runtime VALUE, so TypeScript cannot learn a document's
 * type from it. The guarantee lives where the authority lives — at
 * the decode, against the emitted AST — and a consumer that wants a
 * name for what came back attaches one to a value this codec has
 * already certified, never instead of certifying it.
 */
export type MetaCodec = Schema.Codec<unknown, unknown>

/**
 * CLOSED decoding — the `additionalProperties: false` the emitted JSON
 * Schemas state, spelled where Effect v4 keeps it.
 *
 * `errors: "all"` because a drifted ledger is worth one complete
 * sentence rather than a bisect: the refusal names EVERY offending
 * path, not just the first one the parser reached.
 */
export const closedDecoding: SchemaAST.ParseOptions = {
  errors: "all",
  onExcessProperty: "error",
}

/**
 * THE INTERPRETER: one emitted shape, as an Effect Schema.
 *
 * Seven arms for seven constructors, and a `default` that hands the
 * value to `absurd` — the arm that cannot be reached, and whose
 * argument stops being `never` the moment Lean grows the union. That
 * red is the feature.
 *
 * - `str`   — `Schema.String`.
 * - `nat`   — an integer at or above zero, which is what the emitted
 *             JSON Schema's `{"type": "integer", "minimum": 0}` says.
 * - `bool`  — `Schema.Boolean`.
 * - `enum`  — the exact spellings, as literals; anything else refuses.
 * - `array` — the item shape, interpreted.
 * - `record`— a struct, CLOSED under `closedDecoding`, whose `opt`
 *             fields become optional KEYS (see `structField`).
 * - `opt`   — outside a field position an optional shape can only mean
 *             a value that may be undefined, so that is what it is.
 *             Inside one — where every `opt` in the emitted shapes
 *             actually sits — the record arm reaches the inner shape
 *             first and this arm is never taken.
 */
export const toEffectSchema = (ast: MetaSchema): MetaCodec => {
  switch (ast._tag) {
    case "str":
      return Schema.String
    case "nat":
      return Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))
    case "bool":
      return Schema.Boolean
    case "enum":
      return Schema.Literals(ast.values)
    case "array":
      return Schema.Array(toEffectSchema(ast.items))
    case "record": {
      const fields: Record<string, StructEntry> = {}
      for (const field of ast.fields) {
        fields[field.name] = structField(field)
      }
      return Schema.Struct(fields)
    }
    case "opt":
      return Schema.UndefinedOr(toEffectSchema(ast.inner))
    default:
      return absurd(ast)
  }
}

/** A struct entry the interpreter can build: a shape, or a shape at a
 * key that may be absent. Spelled over `MetaCodec` rather than
 * `Schema.Top` because the plane's schemas need NO SERVICES to decode
 * — a document is bytes, and `Schema.Top` would leave that open. */
type StructEntry = MetaCodec | Schema.optionalKey<MetaCodec>

/** One `record` field as a struct entry. A field whose shape is `opt`
 * becomes an OPTIONAL KEY — absent from the document, not present and
 * null — which is exactly what the emitted JSON Schema says by leaving
 * the name out of its `required` list. */
const structField = (field: MetaField): StructEntry =>
  field.schema._tag === "opt"
    ? Schema.optionalKey(toEffectSchema(field.schema.inner))
    : toEffectSchema(field.schema)

/**
 * An emitted artifact would not decode: the document on disk is not
 * the shape the plane says it is.
 *
 * The refusal carries the ARTIFACT by name and the offending PATH
 * inside it, because those are the two facts a repair needs — which
 * emitter to re-run, and which field drifted. Both come from the
 * decode itself; nothing here re-derives a diagnosis.
 */
export class MetaArtifactRefused extends Schema.TaggedError<MetaArtifactRefused>()(
  "meta/ArtifactRefused",
  { artifact: Schema.String, reason: Schema.String },
) {
  /** The refusal's own words, where every renderer looks for them.
   * `Schema.TaggedError` leaves `message` empty, and `message` is what
   * a log line and the CLI's user-error fold read. */
  override get message(): string {
    return [
      `${this.artifact} is not the shape the meta plane states for it`,
      ...this.reason.split("\n").map((line) => `  ${line}`),
      "  the shape is emitted: `lake exe emitmeta` over library/cas/tools/MetaShapes.lean",
    ].join("\n")
  }
}

/** One described artifact: the name a refusal says out loud, and the
 * emitted AST value that IS its shape. */
export interface MetaArtifactShape {
  readonly artifact: string
  readonly ast: MetaSchema
}

/** Every artifact the emitted AST describes, each bound to the term
 * that describes it. Named individually rather than as an index so a
 * consumer reaching for a shape the plane does not have is a compile
 * error and not an `undefined`. */
export interface DescribedShapes {
  readonly axioms: MetaArtifactShape
  readonly debts: MetaArtifactShape
  readonly manifest: MetaArtifactShape
  readonly names: MetaArtifactShape
  readonly strata: MetaArtifactShape
  readonly trust: MetaArtifactShape
}

/**
 * THE DESCRIBED SET, as the plane emitted it.
 *
 * Six shapes: the manifest's own, the four meta-plane ledgers whose
 * rows the manifest carries a `schema` reference for, and the
 * grammar's `names.json` — which is described by the same emitter but
 * lands outside the meta home, so the manifest has no row for it.
 *
 * The values are the emitted terms; only the ARTIFACT NAMES are
 * written here, and a name is not a shape.
 */
export const describedShapes: DescribedShapes = {
  axioms: { artifact: "axioms.META.json", ast: axiomsShape },
  debts: { artifact: "debts.META.json", ast: debtsShape },
  manifest: { artifact: "MANIFEST.META.json", ast: manifestShape },
  names: { artifact: "names.json", ast: namesShape },
  strata: { artifact: "strata.META.json", ast: strataShape },
  trust: { artifact: "trust.META.json", ast: trustShape },
}

/** The manifest names a row's shape by the JSON SCHEMA FILE printed
 * from it, so joining a row to its AST term takes one binding from
 * file name back to shape. This is that binding, and it is a table of
 * NAMES — the shapes stay where they were emitted. A reference this
 * table cannot place answers none, which is how a described row the
 * interpreter does not yet know becomes a refusal at the consumer
 * rather than a silently unchecked ledger. */
export const shapeForSchemaRef = (reference: string): Option.Option<MetaArtifactShape> => {
  const file = reference.slice(reference.lastIndexOf("/") + 1)
  switch (file) {
    case "manifest.META.schema.json":
      return Option.some(describedShapes.manifest)
    case "cas-axioms.META.schema.json":
      return Option.some(describedShapes.axioms)
    case "cas-debts.META.schema.json":
      return Option.some(describedShapes.debts)
    case "cas-strata.META.schema.json":
      return Option.some(describedShapes.strata)
    case "cas-trust.META.schema.json":
      return Option.some(describedShapes.trust)
    case "names.META.schema.json":
      return Option.some(describedShapes.names)
    default:
      return Option.none()
  }
}

/**
 * THE DOOR: one artifact's text, decoded through its emitted shape.
 *
 * Fail-closed on both halves — text that is not JSON and JSON that is
 * not the shape are the same kind of finding here, and both come back
 * as `MetaArtifactRefused` naming the artifact and the path. The
 * described JSON codec does the parsing: nothing in this estate spells
 * JSON itself.
 */
export const decodeMetaArtifact = (
  shape: MetaArtifactShape,
  jsonText: string,
): Effect.Effect<unknown, MetaArtifactRefused> =>
  Schema.decodeUnknownEffect(
    Schema.fromJsonString(toEffectSchema(shape.ast)),
    closedDecoding,
  )(jsonText).pipe(
    Effect.mapError((error) =>
      new MetaArtifactRefused({ artifact: shape.artifact, reason: error.message })
    ),
  )

/** The field names a `record` shape declares, in the order the
 * emitter wrote them. Every other constructor declares none, and
 * saying so is an answer rather than an error. */
export const fieldNames = (shape: MetaSchema): ReadonlyArray<string> =>
  shape._tag === "record" ? shape.fields.map((field) => field.name) : []

/** One field's shape, by name, unwrapped through `opt` — so a caller
 * asking what a field holds gets the same answer whether or not the
 * field may be absent. */
export const fieldShape = (shape: MetaSchema, name: string): Option.Option<MetaSchema> => {
  if (shape._tag !== "record") return Option.none()
  const found = shape.fields.find((field) => field.name === name)
  if (found === undefined) return Option.none()
  return Option.some(found.schema._tag === "opt" ? found.schema.inner : found.schema)
}

/** An array shape's item shape. */
export const itemsShape = (shape: MetaSchema): Option.Option<MetaSchema> =>
  shape._tag === "array" ? Option.some(shape.items) : Option.none()

/**
 * One `outputs` row of `MANIFEST.META.json`, as a reader names it.
 *
 * TYPES ONLY — there is no second schema here. `manifestShape` is what
 * decodes the manifest, and these names are a projection of a value
 * `decodeMetaArtifact` has already certified against it. The
 * projection is held to the AST rather than to a memory:
 * `decodeMetaManifest` checks each name below against
 * `manifestShape`'s own field list before the type is attached, so a
 * field Lean renames is a REFUSAL that names it, never an `undefined`
 * arriving at a call site.
 *
 * A row carries `schema` when the plane describes the artifact's
 * shape and `awaiting` when it does not, and never both.
 */
export interface MetaOutputRow {
  readonly path: string
  readonly emitter: string
  readonly schema?: string | undefined
  readonly awaiting?: string | undefined
}

/** The manifest, projected to what a registry reads: the rows. */
export interface MetaManifest {
  readonly outputs: ReadonlyArray<MetaOutputRow>
}

/** The names `MetaOutputRow` reads off one row. */
const projectedRowNames: ReadonlyArray<string> = ["path", "emitter", "schema", "awaiting"]

/** Does `manifestShape` still declare everything `MetaManifest`
 * projects? Computed once, from the emitted term — the check that
 * earns the projection its type. */
const manifestProjectionHolds: boolean = fieldNames(manifestShape).includes("outputs")
  && Option.match(Option.flatMap(fieldShape(manifestShape, "outputs"), itemsShape), {
    onNone: () => false,
    onSome: (row) => {
      const declared = fieldNames(row)
      return projectedRowNames.every((name) => declared.includes(name))
    },
  })

/**
 * THE PLANE'S REGISTRY, decoded: `MANIFEST.META.json` read through its
 * own emitted shape, projected to its rows.
 *
 * Two refusals, and they mean different things. The document not
 * matching `manifestShape` is the emitter and the interpreter
 * disagreeing about a document. The SHAPE not declaring what this
 * projection reads is the interpreter and its own consumers
 * disagreeing — a field renamed in Lean, caught before a single row is
 * read rather than surfacing as a registry full of `undefined`.
 */
export const decodeMetaManifest = (
  jsonText: string,
): Effect.Effect<MetaManifest, MetaArtifactRefused> =>
  decodeMetaArtifact(describedShapes.manifest, jsonText).pipe(
    Effect.flatMap((document) =>
      manifestProjectionHolds
        // The one narrowing on the plane, and it is EARNED: the value
        // has just been decoded against `manifestShape` itself, and
        // the guard above says that shape still declares every name
        // this type spells. Nothing is assumed about the bytes.
        ? Effect.succeed<MetaManifest>(cast(document))
        : Effect.fail(
          new MetaArtifactRefused({
            artifact: describedShapes.manifest.artifact,
            reason: `the emitted shape no longer declares outputs[].{${
              projectedRowNames.join(", ")
            }}, which this registry reads`,
          }),
        )
    ),
  )

/** A row's shape, if the plane describes one — the join from a
 * manifest row to the AST term the registry decodes that artifact
 * with. A row that is `awaiting` answers none, and so does one whose
 * schema reference this interpreter cannot place. */
export const shapeForRow = (row: MetaOutputRow): Option.Option<MetaArtifactShape> =>
  Option.flatMap(Option.fromUndefinedOr(row.schema), shapeForSchemaRef)
