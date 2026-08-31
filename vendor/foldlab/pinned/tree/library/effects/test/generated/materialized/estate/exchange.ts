/**
 * GENERATED — do not edit. The ESTATE-NATIVE materialization of the
 * canonical schema node `exchange`, lowered from its committed
 * payload (`library/cas/schemas/exchange.json`) by
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
 *   - exchange — 80f7a642c632bf435bd1a30de1466624abd1c3b69cfc1d96ef75d2bff752daf4
 *
 * emitted — schemaVersion 1, emitter `materialize`,
 * module `library/cas/tools/Materialize.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"
import * as CanonicalSchema from "../../../../src/cas/CanonicalSchema.ts"

/** The canonical code stored at `80f7a642c632bf435bd1a30de1466624abd1c3b69cfc1d96ef75d2bff752daf4`. */
export const exchange = Schema.Struct({
  answer: Schema.String,
  prompt: Schema.String,
  subject: Schema.Union([
    Schema.Struct({
      _tag: Schema.Literal("exchange"),
      address: CanonicalSchema.ref(88),
    }),
    Schema.Struct({
      _tag: Schema.Literal("schema"),
      address: CanonicalSchema.ref(83),
    }),
  ], { mode: "oneOf" }),
})
