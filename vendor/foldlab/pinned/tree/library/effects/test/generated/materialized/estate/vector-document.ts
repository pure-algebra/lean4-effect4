/**
 * GENERATED — do not edit. The ESTATE-NATIVE materialization of the
 * canonical schema node `vector-document`, lowered from its committed
 * payload (`library/cas/schemas/vector-document.json`) by
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
 *   - vectorDocument — cf674c2dfdbd3582661e2f96a026969d31956880a8912f7c1ddd1bb613ad968c
 *
 * emitted — schemaVersion 1, emitter `materialize`,
 * module `library/cas/tools/Materialize.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"

/** The canonical code stored at `cf674c2dfdbd3582661e2f96a026969d31956880a8912f7c1ddd1bb613ad968c`. */
export const vectorDocument = Schema.Struct({
  description: Schema.String,
  digest: Schema.Literal("sha256-scheme0"),
  name: Schema.String,
  schemaVersion: Schema.Literal(1),
  word: Schema.Array(Schema.Struct({
    address: Schema.String,
    node: Schema.Struct({
      payload: Schema.String,
      refs: Schema.Array(Schema.Struct({
        expectedTag: Schema.Int,
        id: Schema.String,
      })),
      tag: Schema.Int,
      version: Schema.Int,
    }),
  })),
})
