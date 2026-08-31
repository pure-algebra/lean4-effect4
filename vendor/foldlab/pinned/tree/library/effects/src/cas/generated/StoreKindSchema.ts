/**
 * GENERATED — do not edit. THE DESCRIBED STORE KINDS, as Effect
 * Schema: the exchange kind and the sidecar annotation kind, lowered
 * from the Lean codes in `library/cas/Cas/Schema/Exchange.lean` and
 * `library/cas/Cas/Schema/Annotation.lean` (`Described.code` of the
 * authored kinds) by `lake exe schemas`; regeneration is
 * byte-identity-gated (`--check`, wired into `check:cas`).
 *
 * These are LIVE codecs, not comparison mirrors: a reference lowers
 * to `refWithTag`, so a value built here encodes a `Root` to a
 * reference sentinel and decodes one back, and the store's admission
 * law checks the arm's kind tag at the address. Their canonical
 * payloads are the committed `schemas/exchange.json` and
 * `schemas/annotation.json`, and the pin suites hold these
 * declarations to those bytes and to the addresses beside them.
 *
 * `src/cas/Exchanges.ts` and `src/cas/Annotations.ts` are this
 * file's consumers. What they add is what a schema is not: the
 * constructors that build one subject arm or one value arm, and —
 * on the annotation side — the estate's persistent annotation
 * namespace on live Effect carriers, which is a different plane
 * with the same name.
 *
 * emitted — schemaVersion 1, emitter `schemas`,
 * module `library/cas/tools/Schemas.lean`, toolchain Lean 4.33.1.
 */
import { Schema } from "effect"
import { Byte } from "../Node.ts"
import { refWithTag } from "../Value.ts"

/** The kind tag exchange nodes reside at
 * (`Cas.Schema.exchangeKindTag`). A WORKING tag, deliberately
 * absent from the reserved set: minting plane identity is the
 * reserved-tag ruling's question, and until it is answered an
 * exchange resides at a tag its callers own — which is what lets
 * `Cas.value` accept it. The `exchange` arm of the subject union
 * demands this tag, so a chain is only walkable when its nodes
 * reside here; that constraint is the whole content of the
 * ruling. */
export const ExchangeKindTag = 88

/** What one exchange is about, by plane: a schema node, or the
 * exchange that came before it. A reference demands ONE kind tag
 * and "what this exchange was about" is genuinely alternatives, so
 * the arms are addressed references, and following the `exchange`
 * arm to exhaustion IS the conversation. A derived union's mode is
 * part of its identity, so the mode is always spelled; member order
 * is the deriving handler's canonical order, and reordering it
 * would be a different code. */
export const exchangeSubjectSchema = Schema.Union([
  Schema.Struct({
    _tag: Schema.Literal("exchange"),
    address: refWithTag(Byte.make(88)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("schema"),
    address: refWithTag(Byte.make(83)),
  }),
], { mode: "oneOf" })

/** One recorded turn of the agent seam (R15): the word put to the
 * model, the answer that came back, and the content the exchange
 * was about. The answer's bytes are kept AS SPOKEN — under the
 * acquisition loop a model's output is evidence and carries no
 * trust, so normalizing it here would destroy the thing a later
 * gate has to judge. No `role` field is spelled: role is a property
 * of an UTTERANCE and an exchange is the PAIR, so position already
 * says which side spoke. */
export const exchangeSchema = Schema.Struct({
  answer: Schema.String,
  prompt: Schema.String,
  subject: exchangeSubjectSchema,
})

/** What one annotation is about, by plane: every addressable plane
 * the estate has today, each arm a typed reference at that plane's
 * tag. The subject was a bare schema reference, which made a view's
 * link to the value it projects, a program's human-facing name and
 * a topology's link to written code all unspellable at once. It
 * then stopped at the meta and agent planes, which left an
 * annotation about STORED CONTENT — and a note about a note —
 * equally unspellable; decision 40's rider CA-1 widened it to the
 * content planes and to the four sorts that batch ratified. No
 * `text` arm: the CRDT run was refused from the batch, so there is
 * no tag for an arm to demand. Nothing is reserved for a plane that
 * does not exist yet: growth is by an arm, and an arm is
 * arm-additive. */
export const annotationSubjectSchema = Schema.Union([
  Schema.Struct({
    _tag: Schema.Literal("agent"),
    address: refWithTag(Byte.make(73)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("annotation"),
    address: refWithTag(Byte.make(65)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("chunk"),
    address: refWithTag(Byte.make(8)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("context"),
    address: refWithTag(Byte.make(13)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("exchange"),
    address: refWithTag(Byte.make(88)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("file"),
    address: refWithTag(Byte.make(11)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("git"),
    address: refWithTag(Byte.make(71)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("program"),
    address: refWithTag(Byte.make(15)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("query"),
    address: refWithTag(Byte.make(81)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("result"),
    address: refWithTag(Byte.make(82)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("schema"),
    address: refWithTag(Byte.make(83)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("system"),
    address: refWithTag(Byte.make(84)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("value"),
    address: refWithTag(Byte.make(1)),
  }),
], { mode: "oneOf" })

/** What one annotation SAYS: a scalar, or a typed reference to
 * addressed content. The value was a plain string, and the kind's
 * own docstring admitted the cost — "a content address in hex when
 * the value is itself store content" — which is precisely the
 * out-of-band config a content-addressed estate exists to remove: a
 * hex string never reaches the reference count, the graph walk
 * never follows it, and a wrong-kind refusal can never fire on it.
 * The `ref` arm carries the subject union rather than a bare
 * reference because a reference must name its expected tag, so a
 * single generic arm cannot be spelled and a second flattened copy
 * of the plane list would drift from the first. */
export const annotationValueSchema = Schema.Union([
  Schema.Struct({
    _tag: Schema.Literal("ref"),
    address: annotationSubjectSchema,
  }),
  Schema.Struct({
    _tag: Schema.Literal("text"),
    text: Schema.String,
  }),
], { mode: "oneOf" })

/** The sidecar annotation kind: one annotation node says one thing
 * about one addressed value, and the DAG carries as many per
 * subject as wanted. Annotation content is STORE CONTENT — nothing
 * is added to the schema carrier. Every reference decodes to a
 * `Root` and encodes to a reference sentinel, so the declaration
 * this lowers to — what the byte pin compares against the Lean
 * fixture — is also the live reference codec the value plane
 * rides. */
export const annotationSchema = Schema.Struct({
  key: Schema.String,
  subject: annotationSubjectSchema,
  value: annotationValueSchema,
})
