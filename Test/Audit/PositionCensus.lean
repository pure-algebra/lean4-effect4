import Effect4.Laws.Auto.Positions
import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Auto.PositionGate

/-!
# The position census of the reference machine

The driver: `lake build Test.Audit.PositionCensus` prints the positions reachable from the
four roots of the typed-state invariant, the write sites of every step root over those
positions, and the read sites. The printed rows are diagnostics; the structured results of the scanner are the
interface. No printed table is read back as authority. Nothing is changed.
-/

open Effect4.Laws.Auto.Positions

#position_census Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
  Effect4.Program.Sched.RInterp Effect4.Program.Sched.RIter

#write_census Effect4.Machine.driveStep closure over Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
#write_census Effect4.Program.Sched.evaluateR closure over Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
#write_census Effect4.Program.Sched.popR closure over Effect4.Program.Sched.RState
#write_census Effect4.Machine.fireObserver closure over Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
#write_census Effect4.Machine.exitFiber closure over Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
#write_census Effect4.Machine.stepDecisionState closure over Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd

#read_census Effect4.Machine.driveStep closure over Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd

#edge_census Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd Effect4.Program.Sched.RIter

/-! ## The totality gate -/

open Effect4.Laws.Auto.PositionGate in
#position_gate Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
  Effect4.Program.Sched.RInterp Effect4.Program.Sched.RIter

