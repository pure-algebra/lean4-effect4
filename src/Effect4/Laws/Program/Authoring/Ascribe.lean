import Effect4.Program.Authoring.Ascribe
import Effect4.Laws.Program.Authoring.Records
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Authoring.Ascribe — an ascription keeps the scope judgment

`ascribe ty e` (`src/Effect4/Program/Authoring/Ascribe.lean`) is a record's construction and a
field's read. It binds no name, so it is scoped where its term is: one application of the two
record lemmas (`src/Effect4/Laws/Program/Authoring/Records.lean`). The lemma is named so that
`authoring_scoped` finds it.

Placement. Concept `initial-algebras-folds`, requirement R4: a step of the claim
`operation-data-scoped` at the surface an author writes. Its consumer is the scope proof of a
client that writes a term at a declared type: a typed empty cell first. It establishes no typing
and no behaviour: those are `types_ascribe` and `reads_ascribe`
(`src/Effect4/Laws/Modules/Ascribe.lean`).

Why the form's four laws stand in two files. The role register
(`tools/Tools/ArchitectureRoles.lean`) puts this folder below `src/Effect4/Laws/Modules`, where
the judgments `Types` and `Reads` live. So the scope lemma stands here, among the scope laws of
the authoring surface, and the three laws over those judgments stand above it.
-/

set_option autoImplicit false

namespace Effect4.Program.Authoring

open Effect4.Program

/-- An ascription is scoped where its term is: the declared type introduces no variable. -/
@[semantics "initial-algebras-folds" (requirement := R4)]
theorem ascribe_scoped (ty : Ty) {e : TermSrc} (h : e.Scoped) : (ascribe ty e).Scoped :=
  field_scoped
    (record_scoped (ascribeFields ty) fun entry member => by
      cases List.mem_singleton.mp member
      exact h)
    "v"

end Effect4.Program.Authoring
