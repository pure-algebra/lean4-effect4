import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive

/-!
Seat F probe (2026-10-01, landing item 1): the census and the `Ty` exhaustiveness inventory with
the repaired instrument, run with the driver's imports (`Test/Audit/TraversalCensus.lean`), and the
four red controls of the brief (`Ty.sub` wf, `ofNormalized` private, `Ty.isFactor` one-level
through a sparse `casesOn`, `Ty.closed` structural). Nothing asserted here; the driver asserts.
-/

#traversal_class Effect4.Program.Ty for Effect4.Program.Ty.sub Effect4.Codegen.Types.ofNormalized Effect4.Program.Ty.isFactor Effect4.Program.Ty.closed

#traversal_census Effect4.Program.Eff
#traversal_census Effect4.Program.Ty
#traversal_census Effect4.Program.Term
#traversal_census Effect4.Representation
#traversal_census Effect4.Store.Val

#exhaustive_gate Effect4.Program.Ty
