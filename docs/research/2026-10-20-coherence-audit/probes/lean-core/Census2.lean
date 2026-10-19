import Effect4
import Effect4.Laws.Auto.Traversals

/-! Probe (coherence audit, lean core, 2026-10-19): the program sort and the type sort, read in the
program and data plane. Read-only. -/

#traversal_census Effect4.Program.Eff under Effect4.Program
#traversal_census Effect4.Program.Eff under Effect4.Schema
#traversal_census Effect4.Program.Eff under Effect4.Store
#traversal_census Effect4.Program.Ty under Effect4.Program
#traversal_census Effect4.Program.Ty under Effect4.Schema
#traversal_census Effect4.Program.Ty under Effect4.Store
#traversal_census Effect4.Program.Ty under Effect4.Tool
#traversal_census Effect4.Program.Ty under Effect4.Run
#traversal_census Effect4.Program.Ty under Effect4.Api
