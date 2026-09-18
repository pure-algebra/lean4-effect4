import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals

/-!
# The traversal census — how every definition reads each free object

Builds print the census (`lake build Test.Audit.TraversalCensus`); nothing is asserted. The
`structural` and `wf` rows of each census are the exemption list of the principle "every
traversal is a fold"; the count is the distance from it. Read against
`docs/core/ontology.md` §5.
-/

#traversal_census Effect4.Program.Eff
#traversal_census Effect4.Program.Ty
#traversal_census Effect4.Program.Term
#traversal_census Effect4.Representation
#traversal_census Effect4.Store.Val
