/**
 * The estate's persistent annotation namespace on Effect Schema.
 *
 * Store metadata rides annotations, never constructors, and only string
 * keys survive: `pruneAnnotations` drops symbol-keyed and non-JSON entries
 * at persistence and code generation
 * (`SchemaRepresentation.ts:927`). Every key here therefore sits under
 * `foldlab/cas/` — a plain slash namespace, open by design, and never the
 * reserved `~*` space Effect keeps for itself.
 *
 * Two attachment facts decide the whole surface, and both are Effect's,
 * not ours:
 *
 * 1. **The representation lowers the ENCODED side.** `toRepresentation`
 *    walks `getLastEncoding`, so an annotation attached to the type side
 *    of a transformation never reaches the persisted document. Attachment
 *    goes through `Schema.annotateEncoded`.
 * 2. **`annotate` lands on the LAST CHECK when checks exist**
 *    (`SchemaAST.annotate`), and resolution reads that same slot
 *    (`internal/schema/annotations.ts:6-8`). Reading `ast.annotations`
 *    directly loses anything attached after a `.check(...)`.
 *
 * `resolveAnnotation` is the single reader that respects fact 2, and the
 * only annotation read the CAS plane performs.
 *
 * The namespace has a second face. Annotations that ride the DAG rather
 * than a live carrier are store content: the described sidecar kind,
 * whose subject is a typed reference to whatever addressable plane the
 * annotation is about. That kind is authored once, in Lean
 * (`library/cas/Cas/Schema/Annotation.lean`), and emitted into
 * `generated/StoreKindSchema.ts` by `lake exe schemas`; this module
 * names its three declarations and adds the constructors that build one
 * subject arm and one annotation value. What that replaced was a
 * hand-written twin held to the Lean bytes by a pin — a real gate on a
 * copy, which is a weaker thing than the copy's absence.
 *
 * The two faces are different planes with the same word: the keys above
 * ride LIVE Effect carriers, and the kind below rides the DAG.
 */
import { cast, Option, Predicate, Schema, SchemaAST } from "effect"
import { ContentId } from "./Node.ts"
import { type CasValue, libraryValue, type Root } from "./Value.ts"
import {
  AnnotationKeys,
  AnnotationKindTag as EmittedAnnotationKindTag,
  AnnotationNameKey,
  AnnotationRevision,
  SystemKindTag as EmittedSystemKindTag,
} from "./generated/annotationPlane.ts"
import { KindTagsByName } from "./generated/grammar/kindTags.ts"
import {
  annotationSchema,
  annotationSubjectSchema,
  annotationValueSchema,
} from "./generated/StoreKindSchema.ts"

/** The prefix every persistent foldlab annotation key carries. */
export const Namespace = "foldlab/cas/"

/** The content address of the schema a carrier describes — the first key
 * of the namespace, and the seed of the annotation-borne DAG. */
export const AddressKey = `${Namespace}address`

/** Read one annotation off an AST the way Effect resolves it: the last
 * check's slot when the node carries checks, the node's own slot
 * otherwise. Both slots are consulted, resolution slot first, so a value
 * is found whichever side of a `.check(...)` it was attached on; without
 * that fallback the attachment order silently decides whether the value
 * exists. */
export const resolveAnnotation = (
  ast: SchemaAST.AST,
  key: string | symbol,
): unknown => {
  const resolved = ast.checks === undefined
    ? undefined
    : Reflect.get(ast.checks.at(-1)?.annotations ?? {}, key)
  return resolved === undefined
    ? Reflect.get(ast.annotations ?? {}, key)
    : resolved
}

/** Attach a content address to a carrier so it survives persistence.
 * Encoded-side attachment is the point: the type side is erased from the
 * representation whenever the carrier is a transformation. */
export const annotateAddress = (address: ContentId) =>
<S extends Schema.Top>(schema: S): S["Rebuild"] =>
  Schema.annotateEncoded({ [AddressKey]: address })(schema)

/** The content address a carrier declares, read off its encoded side.
 * A missing or malformed value fails closed as `None`. */
export const addressOf = (schema: Schema.Top): Option.Option<ContentId> => {
  const carried = resolveAnnotation(
    Schema.toEncoded(schema).ast,
    AddressKey,
  )
  return Predicate.isString(carried)
    ? Schema.decodeOption(ContentId)(carried)
    : Option.none()
}

/** The tag `cont` nodes reside at — a published program is a `cont`
 * node at an address (R7), which is what makes a human-facing name on a
 * program spellable at all. Read off the generated registry, never
 * spelled. */
export const ProgramKindTag = KindTagsByName.cont

/** The tag system nodes reside at — the service-topology plane's
 * WORKING tag, owned in Lean by `Cas.Schema.systemKindTag`.
 *
 * It is the EMITTED constant, not a hand-written `0x54`. There is no
 * TypeScript mirror of `SystemNode` — that lane generates layers, it
 * does not ingest topologies — so this plane has no module of its own
 * to hold the number the way `Exchanges.KindTag` sits with the exchange
 * mirror. What it does have is the annotation plane's projection, whose
 * emitter names the tag the Lean union's `system` arm demands and
 * byte-gates it (`lake exe schemas --check`). A second spelling here
 * was a generated fact written out again by hand, and the only drift a
 * byte gate cannot see is the drift it is not looking at.
 *
 * Re-exported rather than consumed straight from the generated module,
 * because the estate's other consumers name this tag through the
 * annotation namespace. Like every working tag it is deliberately
 * absent from `ReservedKindTags`. */
export const SystemKindTag = EmittedSystemKindTag

/** What one annotation is about, by plane.
 *
 * The subject was a bare reference at the schema kind: a schema node
 * and nothing else. A projection of a program, a topology, an exchange
 * or a git object was literally unspellable, which made three separate
 * things impossible at once — a view's link to the value it projects, a
 * program's human-facing name, and a topology's link to written code.
 * A reference demands ONE kind tag, so "which plane" is genuinely
 * alternatives and the answer is a union, on the `Exchanges.Subject`
 * precedent. */
export const Subject = annotationSubjectSchema

/** What one annotation is about. */
export type Subject = typeof Subject.Type

/** What one annotation SAYS.
 *
 * The value was a plain string, and the kind's own docstring admitted
 * what that cost: "a content address in hex when the value is itself
 * store content." A hex string is not an edge. It never reaches
 * `refCount`, `Graph.verify` never walks it, and `WrongKindReference`
 * can never fire on it — which is exactly the out-of-band config a
 * content-addressed estate exists to remove.
 *
 * The `ref` arm carries a `Subject` rather than a bare reference for the
 * reason the subject is a union at all: a reference must name its
 * expected tag, so a single generic arm cannot be spelled, and a second
 * flattened copy of the plane list would drift from the first. Nesting
 * keeps admission checkable — every arm still names its tag, and the
 * store refuses an edge whose target is of another kind. */
export const Value = annotationValueSchema

/** What one annotation says. */
export type Value = typeof Value.Type

/** The sidecar annotation kind — the codec an annotation node is stored
 * through.
 *
 * Annotation content is STORE CONTENT: nothing is added to the schema
 * carrier, and one annotation node says one thing about one addressed
 * value. The DAG carries as many annotations per subject as wanted.
 *
 * Every reference decodes to a `Root` and encodes to a reference
 * sentinel, so the same declaration this schema lowers to — what the
 * byte pin compares against the Lean fixture — is also the live
 * reference codec the value plane rides. */
export const Annotation = annotationSchema

/** One annotation node's value. */
export type Annotation = typeof Annotation.Type

/** An address as the reference an arm decodes to. Nothing is checked
 * here: encode stamps the arm's expected tag into the sentinel, and the
 * store's admission law refuses the edge when the node at that address
 * is of another kind. */
const arm = (address: ContentId): Root<unknown> => cast(address)

/** The annotation is about the schema stored at this address. */
export const onSchema = (address: ContentId): Subject => ({
  _tag: "schema",
  address: arm(address),
})

/** The annotation is about the service topology stored at this address
 * — the arm the NAME SEAT rides. */
export const onSystem = (address: ContentId): Subject => ({
  _tag: "system",
  address: arm(address),
})

/** The annotation is about the published program (`cont` node) stored
 * at this address. */
export const onProgram = (address: ContentId): Subject => ({
  _tag: "program",
  address: arm(address),
})

/** The annotation is about the recorded turn stored at this address. */
export const onExchange = (address: ContentId): Subject => ({
  _tag: "exchange",
  address: arm(address),
})

/** The annotation is about the git object stored at this address. */
export const onGit = (address: ContentId): Subject => ({
  _tag: "git",
  address: arm(address),
})

/* ── the content planes, and the sort event's own four (decision 40) ──
 *
 * Rider CA-1 widened the Lean union past the meta planes: to the
 * CONTENT planes, so an annotation about stored bytes is nameable at
 * all, and to the four sorts the batch ratified, so a note about a
 * note — or about a query, an answer, or an agent — is spellable. Each
 * arm below is the constructor for one of those, and the suite walks
 * the EMITTED table through them: an arm with no constructor here is a
 * red case, never a silently unspellable plane. */

/** The annotation is about the opaque value stored at this address. */
export const onValue = (address: ContentId): Subject => ({
  _tag: "value",
  address: arm(address),
})

/** The annotation is about the chunk stored at this address — where an
 * embedding's vector bytes live. */
export const onChunk = (address: ContentId): Subject => ({
  _tag: "chunk",
  address: arm(address),
})

/** The annotation is about the named file stored at this address. */
export const onFile = (address: ContentId): Subject => ({
  _tag: "file",
  address: arm(address),
})

/** The annotation is about the folded context stored at this address. */
export const onContext = (address: ContentId): Subject => ({
  _tag: "context",
  address: arm(address),
})

/** The annotation is about the ANNOTATION stored at this address — the
 * reflexive rung: notes about notes, tombstones over retracted ones. */
export const onAnnotation = (address: ContentId): Subject => ({
  _tag: "annotation",
  address: arm(address),
})

/** The annotation is about the agent step stored at this address. */
export const onAgent = (address: ContentId): Subject => ({
  _tag: "agent",
  address: arm(address),
})

/** The annotation is about the query spec stored at this address. */
export const onQuery = (address: ContentId): Subject => ({
  _tag: "query",
  address: arm(address),
})

/** The annotation is about the materialized answer stored at this
 * address. */
export const onResult = (address: ContentId): Subject => ({
  _tag: "result",
  address: arm(address),
})

/** The annotation says this text. */
export const text = (text: string): Value => ({ _tag: "text", text })

/** The annotation points at this addressed content — a typed edge the
 * store walks and refuses, where a hex string used to sit. */
export const ref = (address: Subject): Value => ({ _tag: "ref", address })

/** Build the annotation node value that carries `key`/`value` about
 * whatever `subject` addresses. Storing it is
 * `Cas.value({ kindTag, revision, schema: Annotation })`; the node kind
 * an annotation resides at is the caller's, since the annotation plane
 * has no reserved tag of its own. */
export const annotationOn = (subject: Subject) =>
(annotation: {
  readonly key: string
  readonly value: Value
}): Annotation => ({
  key: annotation.key,
  subject,
  value: annotation.value,
})

/** The kind tag annotation nodes reside at — `0x41`, a RATIFIED
 * registry row since decision 40 and a working tag before it. The
 * promotion kept the byte, which is why no stored annotation moved. */
export const KindTag = EmittedAnnotationKindTag

/** The projection revision annotation nodes ride, the Lean pin's own. */
export const Revision = AnnotationRevision

/** The name seat's key, and the rest of the ratified `foldlab/` family
 * (rider CA-2), emitted from the Lean worked pins. A key is a string
 * and the codec could not care which one — ratifying a family is not a
 * narrowing of the carrier, it is the spelling existing once. */
export const NameKey = AnnotationNameKey

/** Every ratified `foldlab/` annotation key, in the order decision 40
 * names them: the name seat first, then related, search-note, pref,
 * embedding, tombstone. */
export const Keys = AnnotationKeys

/** THE annotation projection — the one interpretation of registry row
 * `0x41`.
 *
 * It is `libraryValue` and not `Cas.value` for the reason
 * `Cas.CanonicalSchema` is: the door on `Cas.value` refuses every
 * registry row so that a CALLER-defined projection cannot give a row a
 * second public interpretation, and this is the row's first. Before
 * decision 40 the plane rode a working tag, every consumer built its own
 * `Cas.value({ kindTag: 0x41, … })`, and the tag's ratification is what
 * turned those into the aliasing the door exists against. One projection
 * now, exported here, and its tag and revision are the emitted ones. */
export const Node: CasValue<Annotation> = libraryValue({
  kindTag: KindTag,
  revision: Revision,
  schema: Annotation,
})
