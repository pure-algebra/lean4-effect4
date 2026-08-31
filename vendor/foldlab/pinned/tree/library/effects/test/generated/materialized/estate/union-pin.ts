/**
 * GENERATED — do not edit. The ESTATE-NATIVE materialization of the
 * canonical schema node `union-pin`, lowered from its committed
 * payload (`library/cas/schemas/union-pin.json`) by
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
 *   - unionPin — 98e36f2243f0269fc3165110660f7b8f08a43aaffc450be7b87ca1f4f6005819
 *
 * emitted — schemaVersion 1, emitter `materialize`,
 * module `library/cas/tools/Materialize.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"

/** The canonical code stored at `98e36f2243f0269fc3165110660f7b8f08a43aaffc450be7b87ca1f4f6005819`. */
export const unionPin = Schema.Struct({
  choice: Schema.Union([Schema.String, Schema.Boolean, Schema.Int], { mode: "anyOf" }),
  exact: Schema.Union([Schema.Literal("zebra"), Schema.Literal("alpha")], { mode: "oneOf" }),
  nested: Schema.optionalKey(Schema.Union([Schema.Null, Schema.Union([Schema.Array(Schema.String), Schema.Boolean], { mode: "oneOf" })], { mode: "anyOf" })),
})
