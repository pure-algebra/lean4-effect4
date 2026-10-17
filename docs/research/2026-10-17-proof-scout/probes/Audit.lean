import probes.A
import probes.B
import probes.C
import probes.D
import probes.E
import probes.R
import probes.FGH
import ProofGraph.AxiomAudit

/-!
# The gate's walk over the probes

Each probe is compiled to an olean whose module name is `probes.<name>`, in a directory added to
`LEAN_PATH`; the receipt in `README.md` gives the commands. The audit is the gate's own walk
(`#axiom_audit`, `tools/ProofGraph/AxiomAudit.lean`), never `#print axioms`.
-/

#axiom_audit probes.A probes.B probes.C probes.D probes.E probes.R probes.FGH
