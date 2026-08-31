/**
 * GENERATED — do not edit. The ESTATE-NATIVE materialization of the
 * canonical schema node `literal-pin`, lowered from its committed
 * payload (`library/cas/schemas/literal-pin.json`) by
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
 *   - literalPin — 5461f66ed3a0eeade4cd058d438d24c86c32b28ce1756b4af8297434103f0c04
 *
 * emitted — schemaVersion 1, emitter `materialize`,
 * module `library/cas/tools/Materialize.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"

/** The canonical code stored at `5461f66ed3a0eeade4cd058d438d24c86c32b28ce1756b4af8297434103f0c04`. */
export const literalPin = Schema.Struct({
  a: Schema.Null,
  b: Schema.Literal(true),
  c: Schema.optionalKey(Schema.Literal(-7)),
  d: Schema.Literal("pinned"),
})
