/**
 * GENERATED — do not edit. The ESTATE-NATIVE materialization of the
 * canonical schema node `tuple-pin`, lowered from its committed
 * payload (`library/cas/schemas/tuple-pin.json`) by
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
 *   - tuplePin — 5f281a876efdf63c43a61c07a1422bf4311ed68efb65806a160db7bc80c5e942
 *
 * emitted — schemaVersion 1, emitter `materialize`,
 * module `library/cas/tools/Materialize.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"

/** The canonical code stored at `5f281a876efdf63c43a61c07a1422bf4311ed68efb65806a160db7bc80c5e942`. */
export const tuplePin = Schema.Struct({
  nested: Schema.optionalKey(Schema.Tuple([Schema.Array(Schema.Tuple([Schema.String])), Schema.Null])),
  pair: Schema.Tuple([Schema.String, Schema.Int]),
  plain: Schema.Array(Schema.String),
  withOptional: Schema.Tuple([Schema.Int, Schema.optionalKey(Schema.String)]),
  withRest: Schema.TupleWithRest(Schema.Tuple([Schema.String]), [Schema.Int]),
})
