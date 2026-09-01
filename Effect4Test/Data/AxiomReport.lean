import Effect4.Data.Optic
import Effect4.Data.Row

/-!
# Data.Row kernel dependency report

Every exported theorem in the frozen Data.Row contract appears here.  The
accepted ceiling is exactly the one frozen by the breaker: no dependency,
`propext`, or `propext` together with `Quot.sound`.  In particular, no theorem
may reach `Classical.choice` or a project-local axiom.
-/

#print axioms Effect4.ascending_iff
#print axioms Effect4.Row.mem_def
#print axioms Effect4.Row.mem_insert
#print axioms Effect4.Row.ascending_insert
#print axioms Effect4.Row.mem_normalize
#print axioms Effect4.Row.ascending_normalize
#print axioms Effect4.Row.eq_of_mem_iff
#print axioms Effect4.Row.normalize_of_ascending
#print axioms Effect4.Row.normalize_idempotent
#print axioms Effect4.Row.normalize_duplicate
#print axioms Effect4.Row.not_mem_empty
#print axioms Effect4.Row.mem_singleton
#print axioms Effect4.Row.mem_union
#print axioms Effect4.Row.union_assoc
#print axioms Effect4.Row.union_comm
#print axioms Effect4.Row.union_idem
#print axioms Effect4.Row.union_empty_left
#print axioms Effect4.Row.union_empty_right
#print axioms Effect4.Row.subset_iff
#print axioms Effect4.Row.subset_refl
#print axioms Effect4.Row.subset_trans
#print axioms Effect4.Row.subset_union_left
#print axioms Effect4.Row.subset_union_right

/-! Pure optic combinators used by Schema annotation data. -/

#print axioms Effect4.Lens.Lawful.compose
#print axioms Effect4.Lens.Lawful.toOptional
#print axioms Effect4.Optional.Lawful.compose
#print axioms Effect4.Optional.Lawful.toTraversal
#print axioms Effect4.Traversal.Lawful.compose
