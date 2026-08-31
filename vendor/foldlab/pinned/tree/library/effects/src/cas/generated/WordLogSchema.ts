/**
 * GENERATED — do not edit. The canonical Effect Schema mirrors of the
 * word's wire records — the receipt and the history document — lowered
 * from the Lean codes in `library/cas/Cas/Lang/WordWire.lean`
 * (`Described.code` of the wire structures) by `lake exe emitword`;
 * regeneration is byte-identity-gated (`--check`, wired into
 * `check:cas`). The word log persists rows in this spelling and
 * `cas history --json` answers this document.
 *
 * emitted — schemaVersion 1, emitter `emitword`,
 * module `library/cas/tools/EmitWord.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"

/** One receipt: the persisted record of one admission — seq is the mark (zero-based word index), at is epoch milliseconds on the admitting host's clock. */
export const wordLogEntrySchema = Schema.Struct({
  address: Schema.String,
  at: Schema.Int,
  seq: Schema.Int,
  size: Schema.Int,
  tag: Schema.Int,
})

/** The history document: the word's suffix from a mark, in admission order, with the next mark. */
export const wordHistorySchema = Schema.Struct({
  next: Schema.Int,
  word: Schema.Array(wordLogEntrySchema),
})
