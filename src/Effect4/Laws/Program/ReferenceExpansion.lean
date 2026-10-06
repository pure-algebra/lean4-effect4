import Effect4.Program.Refs
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# Laws/Program/ReferenceExpansion — a well-formed program expands to a program with no reference

`Eff.expandRefs` (`Program/Refs.lean`) replaces each layer reference by the term at its target,
for one more round than the program has reference sites. This module states that the bound is
enough: a program whose layer references are well formed (`Eff.layerRefsWF`) expands to a program
with no reference site (`expanded_refs_nil_of_wf`).

Placement (AGENTS.md, Trust):

- concept initial-algebras-folds (`docs/core/semantics.md` §2.7), requirement R5; the proposed
  registry claim is `reference-expansion-complete`;
- reach: every operation alphabet, one premise (`Eff.layerRefsWF`), the bound of
  `Eff.expandRefs`;
- it does not establish scope, type formation or typing success. It says nothing about a run:
  the compile does not expand, it redirects a reference to its target and shares the layer by
  its path. It does not establish `lower_refines_build` or any equal-observation claim of R8;
- consumers: `typeOfProgram_expandRefs` (`Laws/Program/ReferenceTyping.lean`) and
  `checkTypedProgram_of_hasTy` (`Laws/Program/CheckedTyping.lean`), which each carry the
  conclusion as a premise today.

The design is `docs/research/2026-10-06-seat-REFS-design.md`.
-/

set_option autoImplicit false

namespace Effect4.Program

/-- **A well-formed program expands to a program with no reference site**, at the bound that
`Eff.expandRefs` uses: one more round than the program has reference sites. -/
@[semantics "initial-algebras-folds" (requirement := R5)]
proof_goal expanded_refs_nil_of_wf {Op : Type} (root : Eff Op)
    (valid : root.layerRefsWF = true) : root.expandRefs.refSites [] = []

end Effect4.Program
