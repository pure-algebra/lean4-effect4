import Effect4.Schema.DocumentJson
import Effect4.Laws.Auto.Semantics

/-!
# Laws of the persisted-document reader: completeness against the writer's image

`Effect4/Schema/DocumentJson.lean` proves the reader exact by construction: what it admits is the
input modulo `normJ` (`Representation.ofJson_exact`, claim `document-json-exact`), because it
reads through the re-encode guard (`Reencode.guard_exact`). This module states the other
direction. Every JSON value whose normal form is a writer image is admitted at some nesting bound
(`ofJson_complete`, claim `document-json-complete`), so a refusal at that bound means no
representation writes that JSON, modulo `normJ`.

Placement of the goal `ofJson_image` (AGENTS.md, five points):

1. Concept `exact-codecs` (concept 5 of `docs/core/semantics.md`), its required property that a
   read is an exact embedding: total on its domain, a retraction, exact modulo a named normaliser.
   This is the totality on the image: the guard's one obligation (`Reencode.guard_image`).
2. Question: the claim `document-json-complete` (compatibility), whose pointer `ofJson_complete`
   rests on this goal.
3. Reach: every `Representation`, at some nesting bound; the writer `writeAlg` and the reader
   `readRepresentation`, modulo `normJ`. Decisions row 396 (2) bounds it.
4. It does not establish that the answer is the written representation itself: a non-finite enum
   or key number other than the canonical three is written as its name, so its bits do not come
   back. It establishes nothing at the public reader's fixed bound `depth`, nothing about rc.112's
   decoder, which admits fewer documents, and nothing about the preparation.
5. Unlocks: R3's codec admission for documents that Effect writes. Its consumer is slice A2's
   comparison of the rows' types with rc.112's own documents.
-/

namespace Effect4.Schema.DocumentJson

open Effect4 Effect4.Schema.Codec

/-- **The reader inverts the writer at some bound.** Placement: concept `exact-codecs`, R3, the
claim `document-json-complete`. Route: induction over the representation family through the
generated fold; at each node the tag step is `RepresentationTag.ofTagName_tagName` (or
`CheckTag`'s), and each field lookup reads the sorted entries `normJ` writes (`sortE_perm`; a
node's fixed keys are distinct). Consumer: `ofJson_complete`. -/
@[semantics "exact-codecs" (requirement := R3)]
proof_goal ofJson_image (r : Representation) :
    ∃ fuel r', readRepresentation fuel (normJ r.toJson) = .ok r' ∧
      normJ r'.toJson = normJ r.toJson

/-- **The reader is complete against the writer's image** (claim `document-json-complete`): a JSON
value with a writer image's normal form is admitted at some bound, and what it answers has that
normal form. Proved modulo the goal `ofJson_image`, through the guard's laws
(`Reencode.guard_congr`, `Reencode.guard_image`). Consumer: slice A2's comparison of the rows'
types with rc.112's documents. -/
@[semantics "exact-codecs" (requirement := R3)]
theorem ofJson_complete {j : Json} {r : Representation} (h : normJ j = normJ r.toJson) :
    ∃ fuel r', Reencode.guard normJ Representation.toJson (readRepresentation fuel) notTheImage j
        = .ok r' ∧ normJ j = normJ r'.toJson := by
  obtain ⟨fuel, r', hread, himage⟩ := ofJson_image r
  refine ⟨fuel, r', ?_, ?_⟩
  · rw [Reencode.guard_congr h]
    exact Reencode.guard_image hread himage
  · rw [h, himage]

end Effect4.Schema.DocumentJson
