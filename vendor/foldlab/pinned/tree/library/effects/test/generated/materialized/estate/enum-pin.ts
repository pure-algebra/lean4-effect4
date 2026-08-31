/**
 * GENERATED — do not edit. The ESTATE-NATIVE materialization of the
 * canonical schema node `enum-pin`, lowered from its committed
 * payload (`library/cas/schemas/enum-pin.json`) by
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
 *   - enumPin — 845c3cfccb9fe60e6bdc4976e3e7e111ec57f2f88ee3bbfb47a7ae447490f15e
 *
 * emitted — schemaVersion 1, emitter `materialize`,
 * module `library/cas/tools/Materialize.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"

/** The canonical code stored at `845c3cfccb9fe60e6bdc4976e3e7e111ec57f2f88ee3bbfb47a7ae447490f15e`. */
export const enumPin = Schema.Struct({
  direction: Schema.Enum({ "Up": "Up", "Down": "Down" }),
  level: Schema.Enum({ "Debug": -1, "Warn": 1, "Warning": 1 }),
  mixed: Schema.optionalKey(Schema.Enum({ "Name": "name", "Zero": 0 })),
})
