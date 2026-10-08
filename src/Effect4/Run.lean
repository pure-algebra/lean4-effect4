import Effect4.Run.Basic
import Effect4.Run.Tape

/-!
# Effect4.Run — the entry module for running a built program (decisions row 332)

A user who runs a program imports this module. It re-exports the run API
(`src/Effect4/Run/Basic.lean`: a run opened from a built program, its rows, its journal and the
reactor's loop) and what a tool reads off a run (`src/Effect4/Run/Tape.lean`: the machine's view,
the raw replay and the tape). It declares nothing.
-/
