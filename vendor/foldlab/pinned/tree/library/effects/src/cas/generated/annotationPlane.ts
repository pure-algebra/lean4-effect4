/**
 * GENERATED — do not edit. THE ANNOTATION PLANE, as data: the tag
 * annotation nodes ride and the everyday word for it, the revision
 * they ride, the ratified `foldlab/` key family, and the subject
 * union's arm-to-tag table, emitted from
 * `library/cas/Cas/Schema/Annotation.lean` by `lake exe schemas`;
 * regeneration is byte-identity-gated (`--check`, wired into
 * `check:cas`). The arm table is read off
 * `AnnotationSubject.schemaCode` — the deriving handler's output —
 * so it widens when the union does and never before. Decision 40
 * widened it by eight arms and ratified the tag, in one event.
 *
 * `src/cas/Annotations.ts` is this file's first consumer: it builds
 * the subject union's arms, exports THE projection annotation nodes
 * are stored through (`Annotations.Node`, at the tag below), and
 * reads the system plane's working tag from here rather than
 * spelling it. `bin/cli/naming.ts` is the second: `cas name` writes
 * through that projection under `AnnotationNameKey`, and refuses
 * subjects on planes this table does not carry. `bin/cli/render.ts`
 * is the third: every everyday kind word the annotation plane owns
 * is seeded from here, so no rendered surface spells one by hand.
 *
 * emitted — schemaVersion 1, emitter `schemas`,
 * module `library/cas/tools/Schemas.lean`, toolchain Lean 4.33.1.
 */

/** One nameable plane: the subject union's arm name, and the wire
 * kind tag a reference through that arm expects at its target. */
export interface AnnotationSubjectArm {
  readonly arm: string
  readonly tag: number
}

/** The tag annotation nodes ride (`pinAnnotationKindTag`).
 * It was a WORKING tag — a byte the callers owned, with no
 * registry row — until decision 40 ratified THAT VERY BYTE as the
 * `annotation` row rather than minting a fresh one, so no stored
 * annotation moved address. It is read off the grammar's sort
 * table in Lean now, which is what makes the promotion a fact of
 * the build. The plane is library-owned, so its projection is
 * `Cas.Annotations.Node` and not a caller's `Cas.value`: the
 * reserved-tag door refuses every registry row, and this row's
 * one interpretation is the library's own. */
export const AnnotationKindTag = 65

/** The everyday word for that kind. It is emitted rather
 * than written in TypeScript because a rendered kind name enters
 * the human register off the generated registry and never off a
 * hand-written table (decision 25). Since decision 40 the kind
 * HAS a registry row, and `tools/EmitGrammar.lean` pins this word
 * to that row's own name, so the overlay and the registry cannot
 * say different words. */
export const AnnotationKindWord = "annotation"

/** The revision annotation nodes ride, the Lean pin's own
 * (`pinAnnotationRevision`) — the projection's revision is part
 * of the wire, so its consumer reads it here. */
export const AnnotationRevision = 1

/** The name seat's annotation key, exactly as the Lean worked
 * example pins it (`pinName`). */
export const AnnotationNameKey = "foldlab/name"

/** THE RATIFIED `foldlab/` KEY FAMILY (decision 40, rider
 * CA-2), read off the Lean worked pins rather than agreed:
 * the name seat, then related, search-note, pref, embedding and
 * tombstone. Keys are structurally OPEN strings — the codec reads
 * `key` as text and could not care which one — so ratifying a
 * family narrows nothing; it makes the spelling exist once, at
 * byte level, the way `foldlab/name` already did. A key not on
 * this list is legal and unratified, which is a different thing
 * from refused. */
export const AnnotationKeys: ReadonlyArray<string> = ["foldlab/name", "foldlab/related", "foldlab/search-note", "foldlab/pref", "foldlab/embedding", "foldlab/tombstone"]

/** The service-topology plane's WORKING tag
 * (`Cas.Schema.systemKindTag`), which the `system` arm below
 * demands at its target. It is emitted HERE because this is the
 * only generated surface in the effects package that names it:
 * the kind registry has no row for a working tag, and the system
 * lane generates layers rather than a node mirror. The day a
 * system mirror lands, this constant moves beside it. Named
 * rather than searched out of the arm table, so its consumer
 * reads a constant the way it reads `KindTagsByName.cont`. */
export const SystemKindTag = 84

/** The nameable planes, in the subject union's own member
 * order: arm name and expected kind tag, read off the union's
 * canonical code. */
export const AnnotationSubjectArms: ReadonlyArray<AnnotationSubjectArm> = [
  {
    arm: "agent",
    tag: 73,
  },
  {
    arm: "annotation",
    tag: 65,
  },
  {
    arm: "chunk",
    tag: 8,
  },
  {
    arm: "context",
    tag: 13,
  },
  {
    arm: "exchange",
    tag: 88,
  },
  {
    arm: "file",
    tag: 11,
  },
  {
    arm: "git",
    tag: 71,
  },
  {
    arm: "program",
    tag: 15,
  },
  {
    arm: "query",
    tag: 81,
  },
  {
    arm: "result",
    tag: 82,
  },
  {
    arm: "schema",
    tag: 83,
  },
  {
    arm: "system",
    tag: 84,
  },
  {
    arm: "value",
    tag: 1,
  },
]
