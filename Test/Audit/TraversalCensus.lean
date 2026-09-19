import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive
import Test.Audit.ExhaustiveFixture

/-!
# The traversal census — how every definition reads each free object

Builds print the census (`lake build Test.Audit.TraversalCensus`); nothing is asserted. The
`structural` and `wf` rows of each census are the exemption list of the principle "every
traversal is a fold"; the count is the distance from it. Read against
`docs/core/ontology.md` §5.

Beside it, the exhaustiveness inventory: which matches on a type have no catch-all, and so
are the definitions a new constructor refuses. It is printed, not asserted, for the same
reason the census is — `docs/core/decisions.md` row 34 keeps the census an instrument, and the
gate over compiled default arms is the case-site policy (`make check-cases`). Read it before
appending a constructor: `lake env lean Test/Audit/TraversalCensus.lean`.

The one assertion here is the inventory's own red control, over
`Test/Audit/ExhaustiveFixture.lean`: a twenty-arm match with no wildcard must be reported
`catchAll false`, the same match closed by `| _ =>` must be reported `catchAll true`, and a
match on `Term` must not be reported at all.
-/

#traversal_census Effect4.Program.Eff
#traversal_census Effect4.Program.Ty
#traversal_census Effect4.Program.Term
#traversal_census Effect4.Representation
#traversal_census Effect4.Store.Val

/--
info: #exhaustive_gate Effect4.Program.Ty (family [Effect4.Program.Ty]) under Test.Audit.ExhaustiveFixture: 2 match(es) read it, 1 with no catch-all — appending a constructor refuses exactly those
  Test.Audit.ExhaustiveFixture.catchAllAbsent	Test.Audit.ExhaustiveFixture	Test.Audit.ExhaustiveFixture.catchAllAbsent.match_1	discr 0	alts 20	catchAll false
  Test.Audit.ExhaustiveFixture.catchAllPresent	Test.Audit.ExhaustiveFixture	Test.Audit.ExhaustiveFixture.catchAllPresent.match_1	discr 0	alts 4	catchAll true
-/
#guard_msgs in
#exhaustive_gate Effect4.Program.Ty under Test.Audit.ExhaustiveFixture

#exhaustive_gate Effect4.Program.Ty
#exhaustive_gate Effect4.Program.Term
#exhaustive_gate Effect4.Store.Val
