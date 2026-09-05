import Effect4.Program.Provision

/-!
Fresh kernel dependency report for the provision algebra
(`src/Effect4/Program/Provision.lean`; plan `docs/research/2026-09-04-provision-algebra.md`).

Coordinator-owned, appended from the `#print axioms` output at each landing. Every theorem
below is expected at the ceiling `propext`/`Quot.sound`; the gate
(`Test/Audit/AxiomGate.lean`) is what enforces it, this file is the human-readable receipt.
-/

-- D0: `Row.diff` and its laws.
#print axioms Effect4.Row.diff
#print axioms Effect4.Row.mem_diff
#print axioms Effect4.Row.diff_subset
#print axioms Effect4.Row.diff_empty
#print axioms Effect4.Row.diff_self
#print axioms Effect4.Row.diff_eq_empty_iff_subset
#print axioms Effect4.Row.diff_union_right
#print axioms Effect4.Row.union_diff_distrib
#print axioms Effect4.Row.diff_subset_diff_left
#print axioms Effect4.Row.diff_subset_diff_right

-- D1: the signature and the provision algebra.
#print axioms Effect4.Program.Provision.LayerTy
#print axioms Effect4.Program.Provision.LayerTy.provide
#print axioms Effect4.Program.Provision.LayerTy.provide_out
#print axioms Effect4.Program.Provision.LayerTy.provideMerge_out
#print axioms Effect4.Program.Provision.LayerTy.provide_requires_subset
#print axioms Effect4.Program.Provision.LayerTy.provide_discharges
#print axioms Effect4.Program.Provision.LayerTy.provide_closed
#print axioms Effect4.Program.Provision.LayerTy.covers_of_provide_closed
#print axioms Effect4.Program.Provision.LayerTy.provide_provide_rows
#print axioms Effect4.Program.Provision.LayerTy.merge_rows_comm
#print axioms Effect4.Program.Provision.LayerTy.merge_requires
#print axioms Effect4.Program.Provision.LayerTy.provide_requires_antitone_out

-- D2: the adjunction and the references.
#print axioms Effect4.Program.Provision.satisfies_iff_subset_keysRow
#print axioms Effect4.Program.Provision.rightBiased_isSome
#print axioms Effect4.Program.Provision.satisfies_merge_left
#print axioms Effect4.Program.Provision.satisfies_merge_right
#print axioms Effect4.Program.Provision.satisfies_union_of
#print axioms Effect4.Program.Provision.satisfies_single_addV
#print axioms Effect4.Program.Provision.satisfiesRefs_of_satisfies
#print axioms Effect4.Program.Provision.satisfiesRefs_of_defaults
#print axioms Effect4.Program.Provision.satisfiesRefs_of_hard

-- D3: the term, its typing, the app.
#print axioms Effect4.Program.Provision.LayerTerm
#print axioms Effect4.Program.Provision.layerTy
#print axioms Effect4.Program.Provision.appTy
#print axioms Effect4.Program.Provision.appTy_requires
#print axioms Effect4.Program.Provision.appTy_closed_iff

-- D4: the specification, its totality, the lowering.
#print axioms Effect4.Program.Provision.build
#print axioms Effect4.Program.Provision.build_total
#print axioms Effect4.Program.Provision.lower
#print axioms Effect4.Program.Provision.runOver
