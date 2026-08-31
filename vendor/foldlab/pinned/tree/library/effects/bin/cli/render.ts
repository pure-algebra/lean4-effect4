/**
 * The two output registers (CLI grill round 2): the human register is
 * a rendering of the content, and `--json` is the described canonical
 * document — the node encoded through the same generated-mirror codec
 * the vectors and the wire speak, rendered sorted-key like the Lean
 * emitter. Nothing here invents a shape.
 *
 * Kind names come from the Lean-emitted registry — `KindTagRows` in
 * `src/cas/generated/grammar/kindTags.ts`, byte-identity-gated by
 * `check:cas`. The hex stays beside the name because the tag is the
 * wire fact and the name is the everyday one, and a reader of `show`
 * needs both: "schema (0x53)". A tag the registry gives no row is
 * printed as bare hex, which is now a statement about that tag rather
 * than about this file.
 *
 * The everyday OVERLAY comes from a second emitted table, on the same
 * law (decision 25: kind names enter the human register off the
 * generated registry, never off a hand-written one). The annotation
 * plane's projection — `src/cas/generated/annotationPlane.ts`, from
 * `Cas/Schema/Annotation.lean`, byte-gated by the same task — carries
 * the subject union's arm words and the word for the annotation kind
 * itself. Those arm words are the reason `cas name`'s kind line and a
 * NotNameable refusal now read the same on one screen: `exchange
 * (0x58)` in both, off one table, rather than a bare byte in one and a
 * spelled plane in the other.
 */
import { Schema } from "effect"
import { Cas } from "../../src/index.ts"
import { canonicalJson } from "../../src/cas/Value.ts"
import { KindTagRows, KindTagsByName } from "../../src/cas/generated/grammar/kindTags.ts"
import {
  AnnotationKindTag,
  AnnotationKindWord,
  AnnotationSubjectArms,
} from "../../src/cas/generated/annotationPlane.ts"

/** A loaded node as the described binding document: the Lean-computed
 * address and the node it binds — the vector wire shape. */
export const toBinding = (
  address: Cas.ContentId,
  node: Cas.NodeInput,
): Cas.ConformanceVector.VectorBinding => ({
  address,
  node: {
    version: node.kind.version,
    tag: node.kind.tag,
    payload: node.payload,
    refs: node.refs.map((ref) => ({ expectedTag: ref.expectedTag, id: ref.id })),
  },
})

/** The `--json` register for one node: encode through the described
 * codec, then render with the ratified canonical printer — compact,
 * keys ordered by codepoint at every depth. These are the bytes the
 * identity is computed over, so the register is not merely
 * machine-readable, it is the content's own spelling. */
export const renderBindingJson = (
  address: Cas.ContentId,
  node: Cas.NodeInput,
): string =>
  canonicalJson(Schema.encodeSync(Cas.ConformanceVector.VectorBinding)(
    toBinding(address, node),
  ))

/** A kind tag in the protocol spelling: bare hex, two digits. */
export const tagHex = (tag: number): string =>
  `0x${tag.toString(16).padStart(2, "0")}`

/** The registry row a tag has, by tag — the generated table indexed
 * once, so no rendering re-spells a number the emitter already owns. */
const kindNames: ReadonlyMap<number, string> = new Map(
  KindTagRows.map((row): readonly [number, string] => [row.tag, row.name]),
)

/** Whether the registry gives this tag a row. A tag with none is still
 * admitted — the store admits every tag at the scheme version — but it
 * is a working tag, and `put` says so. */
export const isRegisteredTag = (tag: number): boolean => kindNames.has(tag)

/**
 * The everyday overlay on the registry names (vocabulary collision 3),
 * seeded from emitted tables and nowhere else.
 *
 * The annotation plane's arm words come first: the words the Lean union
 * spells for the addressable planes, which are everyday words already.
 * Two of those planes — `exchange` (0x58) and `system` (0x54) — have no
 * registry row at all, so before this seeding they rendered as bare hex
 * on one line of a screen whose next line spelled them out. The rest
 * now do have rows, and for those the overlay agrees with the registry
 * rather than overriding it: decision 40's rider CA-1 added arms at
 * `value`, `chunk`, `file`, `context`, `annotation`, `agent`, `query`
 * and `result`, and every one of those arm words IS its row's name.
 *
 * The arm word for the `cont` tag is what carries collision 3's ruling:
 * a `cont` node is never named in a rendered surface — it is the
 * program. A `step` node is one of that program's steps, and the noun
 * it is a step OF is read back out of the overlay rather than spelled
 * again here.
 *
 * Last, the annotation kind's own word, emitted beside its tag. That
 * used to be the only way the word reached a screen, because the plane
 * rode a working tag with no registry row; decision 40 ratified the
 * tag, so `isRegisteredTag` says true now and `put` no longer warns.
 * The seeding stays because it is the pinned pair — `EmitGrammar`
 * holds the emitted word to the row's own name — and because dropping
 * it would move the human register onto a table this file would then
 * have to keep.
 *
 * Only the human register wears any of this. The machine register keeps
 * the registry names, which are the emitted facts.
 */
const everydayNames: ReadonlyMap<number, string> = (() => {
  const overlay = new Map<number, string>(
    AnnotationSubjectArms.map((row): readonly [number, string] => [row.tag, row.arm]),
  )
  const program = overlay.get(KindTagsByName.cont) ?? kindNames.get(KindTagsByName.cont)
  if (program !== undefined) overlay.set(KindTagsByName.step, `${program} step`)
  overlay.set(AnnotationKindTag, AnnotationKindWord)
  return overlay
})()

/** A kind in the everyday register: its name with the wire byte beside
 * it, `schema (0x53)` — the everyday word where the vocabulary rules
 * one (`program (0x0f)`), the registry's name otherwise. A tag the
 * registry gives no row has no name to print, so it renders as the
 * byte alone. */
export const tagLabel = (tag: number): string => {
  const name = everydayNames.get(tag) ?? kindNames.get(tag)
  return name === undefined ? tagHex(tag) : `${name} (${tagHex(tag)})`
}

/**
 * A kind in the machine register: the registry name when there is one,
 * the wire tag as a number, and whether the registry gives it a row —
 * spelled so an agent does not have to parse `schema (0x53)` back
 * apart. The everyday overlay is prose-only on purpose: `name` here is
 * the emitted registry's own word (`cont`, `step`), because the machine
 * register reports emitted facts, not renderings of them.
 */
export const kindJson = (tag: number, version: number): Schema.Json => ({
  name: kindNames.get(tag) ?? null,
  registered: isRegisteredTag(tag),
  tag,
  version,
})

/** THE `--json` printer for every verb: the ratified canonical one, so
 * the machine register is compact and its keys are ordered by codepoint
 * at every depth — one shape, whoever is reading. The argument is
 * `Schema.Json` and not `unknown`, so a verb that tried to print
 * something with no JSON spelling would not compile. */
export const renderJson = (value: Schema.Json): string => canonicalJson(value)

/** A store refusal in the everyday register: every clause named, in
 * the words VOCABULARY.md pins — link, kind, address, store. The fold
 * is the library's own, so a new clause cannot slip through unworded. */
export const casErrorMessage: (error: Cas.Error) => string = Cas.matchError({
  // Ruling ask R5: verification recomputes the address with the
  // AMBIENT scheme, so under a second same-width scheme every
  // cross-scheme read arrives here — and a message naming only
  // corruption would send that reader looking for a disk fault. Both
  // readings are named, and the bound that decides between them today
  // is named with them, so the sentence stays true when the second
  // scheme lands and stays useful before it does. Continuation lines
  // carry the formatter's two-space indent, like every other multi-line
  // refusal in this CLI.
  AddressMismatch: (error) =>
    [
      `refused: the bytes stored at ${error.expected} hash to ${error.actual}`,
      "  the content is corrupt, or it was written under a different address scheme",
      "  one address scheme exists today, so corruption is the live reading",
      "  cas verify names every other node reachable from a root that fails the same check",
    ].join("\n"),
  ContentNotFound: (error) => `nothing in the store at ${error.id}`,
  DanglingReference: (error) =>
    `refused: a link points at ${error.missing}, which is not in the store`,
  NonCanonicalBytes: (error) =>
    `refused: the bytes at ${error.id} are not canonical — the store never renormalizes on read`,
  StoreFailure: (error) => `the store could not answer: ${error.reason}`,
  UnknownKind: (error) =>
    `refused: unknown kind ${tagLabel(error.tag)} at scheme ${error.version}`,
  WrongKindReference: (error) =>
    `refused: a link to ${error.ref} expects kind ${tagLabel(error.expectedTag)}, but that address holds kind ${tagLabel(error.actualTag)}`,
})

/**
 * Stored text, made safe to print INLINE — beside a node's own facts,
 * in a column.
 *
 * `cas name` refuses to write a name carrying a control character, so
 * nothing this CLI stores reaches here needing the escape. But the
 * annotation plane is a library API and the store only grows: a name
 * written another way, or one that arrived over the wire, is content
 * like any other and `show` still has to render it. Unescaped, a stored
 * `\n` would print a second line under the node's facts that reads as
 * something cas said — the store's content forging the tool's own
 * voice. Escaped, it is visibly what it is.
 *
 * The three that have spellings get them; the rest render as their
 * code point, because a name is not a payload and there is nothing to
 * fall back to.
 */
export const inlineText = (text: string): string =>
  text.replaceAll(/\p{Cc}/gu, (character) => {
    const spelled = { "\n": "\\n", "\r": "\\r", "\t": "\\t" }[character]
    return spelled
      ?? `\\u${(character.codePointAt(0) ?? 0).toString(16).padStart(4, "0")}`
  })

/** Printable ASCII only. A payload with any other byte renders as hex:
 * the human register never guesses at an encoding it cannot show. */
const printable = /^[ -~\n\t]*$/u

/** Lenient on purpose: invalid UTF-8 becomes U+FFFD, which the
 * printable test then rejects — so the decision needs no exception. */
const utf8 = new TextDecoder("utf-8")

const hex = (bytes: Uint8Array): string =>
  Array.from(bytes, (byte) => byte.toString(16).padStart(2, "0")).join("")

/** The human payload rendering: text when it decodes and prints, hex
 * otherwise, truncated either way. `--json` carries the exact bytes. */
export const renderPayload = (payload: Uint8Array): string => {
  if (payload.length === 0) return "(empty)"
  const text = utf8.decode(payload)
  const shown = printable.test(text) ? text : hex(payload.slice(0, 48))
  const truncated = shown.length > 96 ? `${shown.slice(0, 96)}...` : shown
  return `${truncated.replaceAll("\n", "\\n")}  (${payload.length} bytes)`
}
