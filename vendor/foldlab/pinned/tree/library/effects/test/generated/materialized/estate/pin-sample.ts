/**
 * GENERATED — do not edit. The ESTATE-NATIVE materialization of the
 * canonical schema node `pin-sample`, lowered from its committed
 * payload (`library/cas/schemas/pin-sample.json`) by
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
 *   - pinSample — 0ee1758ef14781a52a56e9e2d7951555d5af19a9eb7cb9238808ed39d782219e
 *
 * emitted — schemaVersion 1, emitter `materialize`,
 * module `library/cas/tools/Materialize.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"
import * as CanonicalSchema from "../../../../src/cas/CanonicalSchema.ts"

/** The canonical code stored at `0ee1758ef14781a52a56e9e2d7951555d5af19a9eb7cb9238808ed39d782219e`. */
export const pinSample = Schema.Struct({
  count: Schema.Int,
  flag: Schema.Boolean,
  items: Schema.Array(Schema.String),
  label: Schema.String,
  note: Schema.optionalKey(Schema.String),
  root: CanonicalSchema.ref(9),
  unit: Schema.Null,
})
