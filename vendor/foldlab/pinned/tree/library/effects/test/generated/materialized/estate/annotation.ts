/**
 * GENERATED — do not edit. The ESTATE-NATIVE materialization of the
 * canonical schema node `annotation`, lowered from its committed
 * payload (`library/cas/schemas/annotation.json`) by
 * `lake exe materialize` through the estate's own printer
 * (`Cas/Backend/EmitAst.lean`, `Cas/Backend/Ts.lean`); regeneration
 * is byte-identity-gated (`--check`, wired into `check:cas`).
 *
 * This is the SECOND REGISTER of the P6 differential:
 * `Cas.Materialize.source` prints the same node through Effect's own
 * `toCodeDocument`, and MaterializeDifferential asserts the two
 * modules EVALUATE to one schema. The two texts legitimately differ
 * in spelling; the denotation is the identity.
 *
 * Materialized from a schema node (kind tag 0x53):
 *   - annotation — 89e7f571f3dbc8f49565b2f531f7fce74e24081671399391d1e02d183b6a601a
 *
 * emitted — schemaVersion 1, emitter `materialize`,
 * module `library/cas/tools/Materialize.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"
import * as CanonicalSchema from "../../../../src/cas/CanonicalSchema.ts"

/** The canonical code stored at `89e7f571f3dbc8f49565b2f531f7fce74e24081671399391d1e02d183b6a601a`. */
export const annotation = Schema.Struct({
  key: Schema.String,
  subject: Schema.Union([
    Schema.Struct({
      _tag: Schema.Literal("agent"),
      address: CanonicalSchema.ref(73),
    }),
    Schema.Struct({
      _tag: Schema.Literal("annotation"),
      address: CanonicalSchema.ref(65),
    }),
    Schema.Struct({
      _tag: Schema.Literal("chunk"),
      address: CanonicalSchema.ref(8),
    }),
    Schema.Struct({
      _tag: Schema.Literal("context"),
      address: CanonicalSchema.ref(13),
    }),
    Schema.Struct({
      _tag: Schema.Literal("exchange"),
      address: CanonicalSchema.ref(88),
    }),
    Schema.Struct({
      _tag: Schema.Literal("file"),
      address: CanonicalSchema.ref(11),
    }),
    Schema.Struct({
      _tag: Schema.Literal("git"),
      address: CanonicalSchema.ref(71),
    }),
    Schema.Struct({
      _tag: Schema.Literal("program"),
      address: CanonicalSchema.ref(15),
    }),
    Schema.Struct({
      _tag: Schema.Literal("query"),
      address: CanonicalSchema.ref(81),
    }),
    Schema.Struct({
      _tag: Schema.Literal("result"),
      address: CanonicalSchema.ref(82),
    }),
    Schema.Struct({
      _tag: Schema.Literal("schema"),
      address: CanonicalSchema.ref(83),
    }),
    Schema.Struct({
      _tag: Schema.Literal("system"),
      address: CanonicalSchema.ref(84),
    }),
    Schema.Struct({
      _tag: Schema.Literal("value"),
      address: CanonicalSchema.ref(1),
    }),
  ], { mode: "oneOf" }),
  value: Schema.Union([
    Schema.Struct({
      _tag: Schema.Literal("ref"),
      address: Schema.Union([
        Schema.Struct({
          _tag: Schema.Literal("agent"),
          address: CanonicalSchema.ref(73),
        }),
        Schema.Struct({
          _tag: Schema.Literal("annotation"),
          address: CanonicalSchema.ref(65),
        }),
        Schema.Struct({
          _tag: Schema.Literal("chunk"),
          address: CanonicalSchema.ref(8),
        }),
        Schema.Struct({
          _tag: Schema.Literal("context"),
          address: CanonicalSchema.ref(13),
        }),
        Schema.Struct({
          _tag: Schema.Literal("exchange"),
          address: CanonicalSchema.ref(88),
        }),
        Schema.Struct({
          _tag: Schema.Literal("file"),
          address: CanonicalSchema.ref(11),
        }),
        Schema.Struct({
          _tag: Schema.Literal("git"),
          address: CanonicalSchema.ref(71),
        }),
        Schema.Struct({
          _tag: Schema.Literal("program"),
          address: CanonicalSchema.ref(15),
        }),
        Schema.Struct({
          _tag: Schema.Literal("query"),
          address: CanonicalSchema.ref(81),
        }),
        Schema.Struct({
          _tag: Schema.Literal("result"),
          address: CanonicalSchema.ref(82),
        }),
        Schema.Struct({
          _tag: Schema.Literal("schema"),
          address: CanonicalSchema.ref(83),
        }),
        Schema.Struct({
          _tag: Schema.Literal("system"),
          address: CanonicalSchema.ref(84),
        }),
        Schema.Struct({
          _tag: Schema.Literal("value"),
          address: CanonicalSchema.ref(1),
        }),
      ], { mode: "oneOf" }),
    }),
    Schema.Struct({
      _tag: Schema.Literal("text"),
      text: Schema.String,
    }),
  ], { mode: "oneOf" }),
})
