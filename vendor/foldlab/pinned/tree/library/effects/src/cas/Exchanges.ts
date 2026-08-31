/**
 * The exchange kind — interactions as content.
 *
 * R15 rules the agent seam SYMMETRIC: an agent programs the store as a
 * client of `CasSig`, and the store programs an agent as a handler of
 * `LlmSig`, where `infer` is an operation whose ANSWER ENTERS ONLY AS
 * RECORDED CONTENT. This module is the stored form of that recording.
 *
 * Nothing here is new theory. An exchange is a described kind like any
 * other: it rides the store's admission law, its references are typed
 * edges the store checks, and the provenance of an answer is the DAG
 * walk the store already performs.
 *
 * The kind itself is no longer written here. It is authored once, in
 * Lean (`library/cas/Cas/Schema/Exchange.lean`), and emitted into
 * `generated/StoreKindSchema.ts` by `lake exe schemas`; this module
 * names those declarations and adds the constructors that build one
 * subject arm and one recorded turn. What that replaced was a
 * hand-written twin held to the Lean bytes by a pin — a real gate on a
 * copy, which is a weaker thing than the copy's absence.
 */
import type { ContentId } from "./Node.ts"
import { cast } from "effect"
import { type Root } from "./Value.ts"
import {
  ExchangeKindTag,
  exchangeSchema,
  exchangeSubjectSchema,
} from "./generated/StoreKindSchema.ts"

/** The kind tag exchange nodes reside at.
 *
 * A WORKING tag, deliberately absent from `ReservedKindTags`: minting
 * plane identity is the reserved-tag ruling's question, and until it is
 * answered an exchange resides at a tag its callers own — which is what
 * lets `Cas.value` accept it. The `exchange` arm of the subject union
 * demands this tag, so a chain is only walkable when its nodes reside
 * here; that constraint is the whole content of the ruling. */
export const KindTag = ExchangeKindTag

/** What one exchange is about, by plane.
 *
 * `subject` is a tagged union rather than a single reference because a
 * reference demands ONE kind tag and "what this exchange was about" is
 * genuinely alternatives: the `schema` arm addresses a schema node, and
 * the `exchange` arm addresses the exchange before it. Following the
 * second arm to exhaustion IS the conversation. */
export const Subject = exchangeSubjectSchema

/** What one exchange is about. */
export type Subject = typeof Subject.Type

/** One recorded turn of the agent seam, and the codec an exchange node
 * is stored through.
 *
 * No `role` field is spelled. Role is a property of an UTTERANCE and an
 * exchange is the PAIR; the seam has one operation and one answer, so
 * position already says which side spoke. */
export const Exchange = exchangeSchema

/** One exchange node's value. */
export type Exchange = typeof Exchange.Type

/** An address as the reference an arm decodes to. Nothing is checked
 * here: encode stamps the arm's expected tag into the sentinel, and the
 * store's admission law refuses the edge when the node at that address
 * is of another kind. */
const arm = (address: ContentId): Root<unknown> => cast(address)

/** The exchange was about the schema stored at this address. */
export const aboutSchema = (address: ContentId): Subject => ({
  _tag: "schema",
  address: arm(address),
})

/** The exchange followed the exchange stored at this address — the edge
 * a conversation is walked along. */
export const aboutExchange = (address: ContentId): Subject => ({
  _tag: "exchange",
  address: arm(address),
})

/** Build the exchange node value recording one turn about `subject`.
 * Storing it is `Cas.value({ kindTag: Exchanges.KindTag, revision,
 * schema: Exchanges.Exchange })` — the `exchange` arm only resolves for
 * chains stored at `KindTag`. */
export const recorded = (subject: Subject) =>
(turn: {
  readonly prompt: string
  readonly answer: string
}): Exchange => ({
  answer: turn.answer,
  prompt: turn.prompt,
  subject,
})
