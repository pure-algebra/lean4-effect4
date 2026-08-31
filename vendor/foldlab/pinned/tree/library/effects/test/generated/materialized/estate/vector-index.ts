/**
 * GENERATED — do not edit. The ESTATE-NATIVE materialization of the
 * canonical schema node `vector-index`, lowered from its committed
 * payload (`library/cas/schemas/vector-index.json`) by
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
 *   - vectorIndex — a5445fde1908dedd1f115104b3853c8fe4146ecac58a0105009c2fb9fafb31f1
 *
 * emitted — schemaVersion 1, emitter `materialize`,
 * module `library/cas/tools/Materialize.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"

/** The canonical code stored at `a5445fde1908dedd1f115104b3853c8fe4146ecac58a0105009c2fb9fafb31f1`. */
export const vectorIndex = Schema.Struct({
  digest: Schema.Literal("sha256-scheme0"),
  schemaVersion: Schema.Literal(1),
  vectors: Schema.Array(Schema.Struct({
    bindings: Schema.Int,
    description: Schema.String,
    file: Schema.String,
    name: Schema.String,
    root: Schema.String,
  })),
})
