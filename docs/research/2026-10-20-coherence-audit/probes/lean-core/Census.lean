import Effect4
import Effect4.Laws.Auto.Traversals

/-! Probe (coherence audit, lean core, 2026-10-19): how the session face and the data plane read
the program sort. Read-only; prints the census rows for the modules in scope. -/

#traversal_census Effect4.Program.Eff under Effect4.Run
#traversal_census Effect4.Program.Eff under Effect4.Tool
#traversal_census Effect4.Program.Eff under Effect4.Api
