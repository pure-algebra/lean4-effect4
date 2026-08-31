/**
 * GENERATED — do not edit. The canonical Effect Schema mirrors of the
 * conformance-vector wire format, lowered from the Lean codes in
 * `library/cas/Cas/Vectors/Schema.lean` (`Described.code` of the
 * wire structures) by `lake exe emitwire`; regeneration is
 * byte-identity-gated (`--check`, wired into `check:cas`). The
 * CanonicalSchemaPin suite compares their native representation bytes
 * against the Lean-emitted fixtures — the drift tripwire, now
 * derived on both sides.
 *
 * emitted — schemaVersion 1, emitter `emitwire`,
 * module `library/cas/tools/EmitWire.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"

/** One typed reference: expected kind tag and hex address. */
export const refSchema = Schema.Struct({
  expectedTag: Schema.Int,
  id: Schema.String,
})

/** One node: scalar header fields, hex payload, ordered references. */
export const nodeSchema = Schema.Struct({
  payload: Schema.String,
  refs: Schema.Array(refSchema),
  tag: Schema.Int,
  version: Schema.Int,
})

/** One binding: the Lean-computed address and the node it binds. */
export const bindingSchema = Schema.Struct({
  address: Schema.String,
  node: nodeSchema,
})

/** A registered conformance vector: metadata plus the store word. */
export const vectorSchema = Schema.Struct({
  description: Schema.String,
  digest: Schema.Literal("sha256-scheme0"),
  name: Schema.String,
  schemaVersion: Schema.Literal(1),
  word: Schema.Array(bindingSchema),
})

/** One index row: where a fixture lives and what its word binds. */
export const indexEntrySchema = Schema.Struct({
  bindings: Schema.Int,
  description: Schema.String,
  file: Schema.String,
  name: Schema.String,
  root: Schema.String,
})

/** The index.json manifest over the Lean vector registry. */
export const indexSchema = Schema.Struct({
  digest: Schema.Literal("sha256-scheme0"),
  schemaVersion: Schema.Literal(1),
  vectors: Schema.Array(indexEntrySchema),
})
