/**
 * The naming seat, spoken from the shell — the CLI's side of the
 * annotation plane.
 *
 * Names are annotations, never identity (backend backlog ruling,
 * decision 23): `cas name` stores one `Annotations.Annotation` node
 * saying `foldlab/name` about an addressed subject, and nothing about
 * the subject moves. Every spelling here is the Lean pin's own
 * (`library/cas/Cas/Schema/Annotation.lean`): the key is `foldlab/name`
 * (`pinName`), the node rides tag 0x41 at revision 1, and the wire is
 * the `Annotation` mirror through the ordinary doors — the library's
 * own projection to put, admission to refuse, `RootStore` to publish.
 *
 * That tag used to be a WORKING one, so this module built its own
 * `Cas.value({ kindTag: 0x41, … })`. Decision 40 ratified the same byte
 * as the `annotation` registry row, and `Cas.value` refuses every
 * registry row — a caller-defined projection at a ratified tag is the
 * aliasing that door exists against. The projection is therefore the
 * library's, `Cas.Annotations.Node`, and this module names it rather
 * than constructing a second one.
 *
 * ## Why a name is PUBLISHED
 *
 * The store has no reverse index: nothing can ask "which nodes point at
 * this address" without walking something. Roots are the one walkable
 * surface the estate already has — "the addresses published as entry
 * points" — and a name exists precisely to be an entry point for a
 * person. So `cas name` publishes the annotation node as a root, which
 * is what lets `cas show <subject>` find it again over EITHER backend,
 * and lets `cas verify` audit the naming plane with everything else.
 * Content addressing makes this idempotent: the same name said twice is
 * the same node, and one root.
 *
 * ## What can be named
 *
 * Only what the ratified subject union spans. `AnnotationSubject` is a
 * `oneOf` union over thirteen addressable planes since decision 40's
 * rider CA-1 — the meta and agent five, the four content planes, and
 * the four sorts that batch ratified — because a reference must declare
 * the kind tag it expects. A plane outside the union is not nameable,
 * and this module says so rather than inventing an arm the Lean twin
 * does not have.
 */
import { Array as Arr, cast, Effect, Option } from "effect"
import { Cas } from "../../src/index.ts"
import { AnnotationSubjectArms } from "../../src/cas/generated/annotationPlane.ts"

/** The name seat's key — the EMITTED spelling (`annotationPlane.ts`,
 * from `Cas/Schema/Annotation.lean`'s own pins, byte-gated), given the
 * house name the CLI reads it under. */
export const NameKey = Cas.Annotations.NameKey

/** The annotation projection — THE one, the library's, at the emitted
 * revision and the emitted tag. Neither number is spelled here, and
 * since decision 40 neither is the projection: a caller-built
 * `Cas.value` at a ratified registry row is refused at the door, and
 * `Cas.Annotations.Node` is the row's one interpretation. */
export const AnnotationNode = Cas.Annotations.Node

/**
 * The nameable planes, exactly as the emitted arm table spells them —
 * the subject union's own member order, arm name and expected kind
 * tag. This is the table the refusal prints, so the message and the
 * union cannot drift apart: a widened union widens the emitted table
 * on regeneration, and the byte gate refuses until it has.
 */
export const nameablePlanes: ReadonlyArray<readonly [string, number]> =
  AnnotationSubjectArms.map((row) => [row.arm, row.tag])

/** An address no store holds, used only to ask a constructor which arm
 * it builds. Cheaper than a second table of arm names, and it cannot
 * disagree with the library the way a table can. */
const probe = Cas.ContentId.make("0".repeat(64))

/** The arm constructors, keyed by the arm each one actually builds —
 * the hand half of the seam, because a constructor is code and the
 * emitted table is data. The KEYS are read off the library's own
 * output rather than spelled here, so this module holds no copy of an
 * arm name; the emitted table holds no copy of a constructor. The
 * suite walks the emitted table through `subjectFor` and fails when an
 * emitted arm has no constructor here, so a widened union cannot ship
 * a refusal that lies about the plane being unspellable. */
const constructors: ReadonlyMap<string, (id: Cas.ContentId) => Cas.Annotations.Subject> =
  new Map([
    Cas.Annotations.onExchange,
    Cas.Annotations.onGit,
    Cas.Annotations.onProgram,
    Cas.Annotations.onSchema,
    Cas.Annotations.onSystem,
    // The content planes and the sort event's own four — decision 40's
    // rider CA-1. Each is here because the walk below fails without it.
    Cas.Annotations.onValue,
    Cas.Annotations.onChunk,
    Cas.Annotations.onFile,
    Cas.Annotations.onContext,
    Cas.Annotations.onAnnotation,
    Cas.Annotations.onAgent,
    Cas.Annotations.onQuery,
    Cas.Annotations.onResult,
  ].map((make): readonly [string, (id: Cas.ContentId) => Cas.Annotations.Subject] =>
    [make(probe)._tag, make]
  ))

/** The subject arm a stored node's kind tag selects, or none when the
 * emitted table has no arm at that plane. */
export const subjectFor = (
  tag: number,
  id: Cas.ContentId,
): Option.Option<Cas.Annotations.Subject> =>
  Option.fromUndefinedOr(AnnotationSubjectArms.find((row) => row.tag === tag)).pipe(
    Option.flatMap((row) => Option.fromUndefinedOr(constructors.get(row.arm))),
    Option.map((make) => make(id)),
  )

/** One annotation found about a subject: the annotation node's own
 * address, and what it says. */
export interface FoundAnnotation {
  readonly annotation: Cas.ContentId
  readonly key: string
  readonly value: Cas.Annotations.Value
}

/** Names first, then other keys, then by annotation address — a stable
 * order for rendering, compared by codepoint so no locale decides it. */
const byNameFirst = (left: FoundAnnotation, right: FoundAnnotation): number => {
  const leftRank = left.key === NameKey ? 0 : 1
  const rightRank = right.key === NameKey ? 0 : 1
  if (leftRank !== rightRank) return leftRank - rightRank
  if (left.key !== right.key) return left.key < right.key ? -1 : 1
  return left.annotation < right.annotation ? -1 : left.annotation > right.annotation ? 1 : 0
}

/**
 * Every published annotation about one address: the roots listing
 * walked, each root read through the annotation projection, and the
 * ones whose subject is this address kept.
 *
 * Best-effort PER ROOT, and only per root: a root of another kind,
 * another revision, or another shape simply is not an annotation about
 * this subject, and the walk moves on — `cas verify` is the verb that
 * judges roots, not this read. But the roots LISTING itself failing is
 * a different fact, and it stays in the error channel: a store that
 * cannot say what it has published has not answered "no names", it has
 * not answered. `show` says so on its own line rather than printing an
 * empty result that reads like an absence of names.
 *
 * The failure type is the listing's own — `BackendFailure`, the only
 * thing `RootStore.list` can raise — and not the whole store error
 * union, because every OTHER refusal on this path is already answered
 * per root above.
 *
 * The cost is one load per published root, which is the honest price of
 * having no reverse index; the day an index kind lands, this walk is
 * what it replaces.
 */
export const annotationsAbout = (
  subject: Cas.ContentId,
): Effect.Effect<
  ReadonlyArray<FoundAnnotation>,
  Cas.BackendFailure,
  Cas.RootStore | Cas.Loader
> =>
  Cas.RootStore.pipe(
    Effect.flatMap((roots) => roots.list),
    Effect.flatMap((published) =>
      Effect.forEach(published, (id) =>
        AnnotationNode.get(cast(id)).pipe(
          Effect.map((annotation) =>
            annotation.subject.address === subject
              ? Option.some({
                  annotation: id,
                  key: annotation.key,
                  value: annotation.value,
                } satisfies FoundAnnotation)
              : Option.none<FoundAnnotation>()
          ),
          Effect.orElseSucceed(() => Option.none<FoundAnnotation>()),
        ))
    ),
    Effect.map((found) => Arr.getSomes(found).toSorted(byNameFirst)),
  )
