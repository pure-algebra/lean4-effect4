import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Program.Typed.PositionGate

/-!
# The position census of the reference machine

The battery holds the totality gate over the positions reachable from the four roots of the
typed-state invariant. The census commands of `Effect4.Laws.Auto.Positions` print the
diagnostics on demand: `#position_census` the positions, `#write_census` and `#read_census` a
step root's write and read sites, `#edge_census` the edges. Run one in a scratch file under
`lake env lean`; a build prints none. No printed table is read back as authority.
-/

/-! ## The totality gate -/

/-- info: 87 positions from 4 roots, 90 source rows
  11	owner
  9	custom
  5	exit
  3	column
  6	journal
  53	hook
  refused	Effect4.Machine.Stores.externals	external rows are the table-aware slice (DI-57); the reference parks them forever -/
#guard_msgs in
open Effect4.Laws.Auto.PositionGate in
#position_gate Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
  Effect4.Program.Sched.RInterp Effect4.Program.Sched.RIter
