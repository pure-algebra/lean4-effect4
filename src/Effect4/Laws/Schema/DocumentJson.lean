import Effect4.Schema.DocumentJson
import Effect4.Laws.Auto.Semantics

/-!
# Laws of the persisted-document reader: completeness against the writer's image

`Effect4/Schema/DocumentJson.lean` proves the reader exact by construction: what it admits is the
input modulo `normJ` (`Representation.ofJson_exact`, claim `document-json-exact`). This module
states the other direction. Every JSON value whose normal form is a writer image is admitted
(`admit_complete`, claim `document-json-complete`), which makes the reader's located refusal
complete against its judgment: a refusal means no representation writes that JSON, modulo
`normJ`, within the bound.

Placement of the goal `admit_image` (AGENTS.md, five points):

1. Concept `exact-codecs` (concept 5 of `docs/core/semantics.md`), its required property that a
   read is an exact embedding: total on its domain, a retraction, exact modulo a named normaliser.
   This is the totality on the image.
2. Question: the claim `document-json-complete` (compatibility), whose pointer `admit_complete`
   rests on this goal.
3. Reach: every `Representation`, at some nesting bound; the writer `writeAlg` and the reader
   `readRepresentation`, modulo `normJ`. Decisions row 396 (2) bounds it.
4. It does not establish that the answer is the written representation itself: a non-finite enum
   or key number other than the canonical three is written as its name, so its bits do not come
   back. It establishes nothing about rc.112's decoder, or about the preparation.
5. Unlocks: R3's codec admission for documents that Effect writes. Its consumer is slice A2's
   comparison of the rows' types with rc.112's own documents, and slice A4's round trip.
-/

namespace Effect4.Schema.DocumentJson

open Effect4 Effect4.Schema.Codec

/-- **Every writer image is admitted**, at some nesting bound. Placement: concept `exact-codecs`,
R3, the claim `document-json-complete`. Route: induction over the representation family through
the generated fold, with the reader's lookups at the sorted fields that `normJ` writes (`sortE`
permutes an object's entries and keeps their keys distinct). Consumer: `admit_complete`. -/
@[semantics "exact-codecs" (requirement := R3)]
proof_goal admit_image (r : Representation) :
    ∃ fuel r', admit Representation.toJson (readRepresentation fuel) r.toJson = .ok r'

/-- **The reader is complete against the writer's image** (claim `document-json-complete`): a JSON
value with a writer image's normal form is admitted, at some bound, and what it answers has that
normal form (`admit_exact`). Proved modulo the goal `admit_image`. Consumer: slice A2's comparison
of the rows' types with rc.112's documents. -/
@[semantics "exact-codecs" (requirement := R3)]
theorem admit_complete {j : Json} {r : Representation} (h : normJ j = normJ r.toJson) :
    ∃ fuel r', admit Representation.toJson (readRepresentation fuel) j = .ok r' ∧
      normJ j = normJ r'.toJson := by
  obtain ⟨fuel, r', hr⟩ := admit_image r
  refine ⟨fuel, r', ?_, ?_⟩
  · rw [admit_congr h]
    exact hr
  · rw [h]
    exact admit_exact hr

end Effect4.Schema.DocumentJson
