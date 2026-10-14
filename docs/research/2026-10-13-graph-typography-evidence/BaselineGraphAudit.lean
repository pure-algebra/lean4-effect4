import Tools.View.Graph
import ProofGraph.AxiomAudit

/-!
Baseline evidence for the graph typography review.
Effect4 source base: f25c74f3e2c6acd2bf4ad85c7cbd205dcc8952e0.
The lane changes research files only after that base.
This command is expected to refuse pre-existing String dependency paths.
It adds no theorem, exemption, or trust change.
-/

#axiom_audit checked Tools.View.Graph

/-!
Receipt: the unchanged Graph sources match the source base above.
Set LEAN_NUM_THREADS=3 and use the executable below under PowerShell.
Executable: C:/Users/kokok/scoop/apps/elan/4.2.3/.elan/bin/lake.exe.
Build command: lake build Tools.View.Graph ProofGraph.AxiomAudit.
Build result: exit 0, 32 jobs.
Audit command: lake env lean -DwarningAsError=true
  docs/research/2026-10-13-graph-typography-evidence/BaselineGraphAudit.lean.
Audit result: expected exit 1, 8 offenders among 461 declarations.
The checked dependency snapshot contains 5758 constants.
Both commands report the existing manifest revision warning.
No dependency update, trust exemption, or production source change occurs.
BaselineGraphAudit.txt retains the audit command's standard output and error output.
-/
