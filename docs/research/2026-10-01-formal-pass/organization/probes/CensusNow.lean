import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive

/-!
Seat ORGANIZATION probe (2026-10-01): the traversal census and the exhaustiveness inventory at
HEAD, run exactly as `Test/Audit/TraversalCensus.lean` runs them (same imports, same commands),
so the numbers can be compared with `docs/core/traversal-census.md` §7.9 (78 hand traversals,
65 with a fold and connector, 13 named exemptions) without building `Test`.
Nothing is asserted; the output is the evidence. Run:
  bash serial.sh lake env lean -M6144 -DwarningAsError=true <this file>
-/

#traversal_census Effect4.Program.Eff
#traversal_census Effect4.Program.Ty
#traversal_census Effect4.Program.Term
#traversal_census Effect4.Representation
#traversal_census Effect4.Store.Val

#exhaustive_gate Effect4.Program.Ty
