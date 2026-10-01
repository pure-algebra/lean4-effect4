import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals
import Test.Audit.TraversalFixture

/-! Seat F probe: the exact text the driver's two new `#guard_msgs` pin (printed, not asserted). -/

#traversal_census Effect4.Program.Ty under Test.Audit.TraversalFixture

#traversal_class Effect4.Program.Ty for Effect4.Program.Ty.sub Effect4.Codegen.Types.ofNormalized Effect4.Program.Ty.isFactor Effect4.Program.Ty.closed
