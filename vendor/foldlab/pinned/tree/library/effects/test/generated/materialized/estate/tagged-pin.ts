/**
 * GENERATED — do not edit. The ESTATE-NATIVE materialization of the
 * canonical schema node `tagged-pin`, lowered from its committed
 * payload (`library/cas/schemas/tagged-pin.json`) by
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
 *   - taggedPin — 90208f8ffb27351f48346c096e93869c633ec58840c91456b7b533f70c65c8d9
 *
 * emitted — schemaVersion 1, emitter `materialize`,
 * module `library/cas/tools/Materialize.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"

/** The canonical code stored at `90208f8ffb27351f48346c096e93869c633ec58840c91456b7b533f70c65c8d9`. */
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
