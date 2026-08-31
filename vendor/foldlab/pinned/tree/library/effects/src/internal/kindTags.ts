/** The library-owned CAS kind tags, in one registry.
 *
 * Every fixed tag the runtime interprets lives here so no two kind
 * planes can collide. `Cas.value` refuses this whole set — a
 * caller-defined projection must never alias a node kind the library
 * already reads.
 *
 * The grammar's own rows are not hand-maintained: they are
 * `GrammarKindTags`, the generated projection of `Cas.Grammar.manifestV0`
 * (byte-gated by `lake exe emitgrammar --check`), so ratifying a sort in
 * Lean widens this door on the next regeneration rather than on
 * someone's memory. Only tags with no registry row are spelled below,
 * and a future one enters here — or, if it is a grammar sort, the Lean
 * table — before any module uses it. */
import {
  GrammarKindTags,
  KindTagsByName,
} from "../cas/generated/grammar/kindTags.ts"

/** Replay histories and witnesses. The replay plane carries no registry
 * row — it is not a data-grammar sort — but its tags are library-owned
 * all the same, so they are refused beside the registry's. */
export const HistoryKindTag = 0x48
export const WitnessKindTag = 0x57

/** The three blob-graph tags, read off their registry rows. */
export const ChunkDataTag = KindTagsByName.chunk
export const BlobNodeTag = KindTagsByName.tree
export const BlobManifestTag = KindTagsByName.manifest
/** Canonical-schema nodes: the schema plane's own kind. */
export const SchemaKindTag = KindTagsByName.schema
/** Git objects as content: the payload is the loose-object preimage,
 * so the git SHA-1 identity is derivable from the payload alone. */
export const GitKindTag = KindTagsByName.git

/** THE refusal set: every ratified and reserved registry tag, plus the
 * two replay-plane tags the registry does not carry. */
export const ReservedKindTags: ReadonlySet<number> = new Set([
  ...GrammarKindTags,
  HistoryKindTag,
  WitnessKindTag,
])
