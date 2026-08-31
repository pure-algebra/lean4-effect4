/**
 * GENERATED — do not edit. THE RESERVED PAYLOAD KEYS of the
 * typed-reference law (CAS-005): the key a stored payload spells a
 * reference with, and the key an encode-side value carries one as
 * before the walk assigns indexes — emitted from
 * `library/cas/Cas/Core/Refs.lean` and
 * `library/cas/Cas/Schema/Codec/References.lean` by
 * `lake exe emitgrammar`; regeneration is byte-identity-gated
 * (`--check`, wired into `check:cas`).
 *
 * `src/internal/refMarkers.ts` is this file's consumer: the two
 * walks it carries are written against these keys, and both REFUSE
 * — never escape — user data that collides with one, because an
 * escape would invent a second spelling for the same value and
 * split its content identity. That is why the keys are emitted
 * rather than agreed: a payload's identity turns on them, and the
 * two sides of the wire cannot be allowed to disagree about which
 * two strings they are.
 *
 * emitted — schemaVersion 1, emitter `emitgrammar`,
 * module `library/cas/tools/EmitGrammar.lean`, toolchain Lean 4.33.1.
 */

/** The marker key. A typed reference appears in a stored
 * payload as exactly `{<this key>: k}`, where k is the index of
 * the k-th marker in canonical byte order — indexes forced,
 * sharing by repeated entries. */
export const RefMarkerKey = "$ref"

/** The sentinel key. An encode-side value carries a
 * reference under this key, as `{id, tag}`, until `markerize`
 * lowers it to a positional marker and an entry in the node's
 * reference array. Read off `Cas.Schema.encRef`, the codec that
 * writes the sentinel, rather than spelled a second time. */
export const RefSentinelKey = "$link"
