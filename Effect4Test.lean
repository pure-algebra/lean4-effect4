import Effect4Test.Algebra.ExtractionContract
import Effect4Test.Algebra.AxiomReport
import Effect4Test.Audit.AxiomGate

/-!
# Effect4 test battery

The default Lake build imports every admitted contract, attack, and kernel
dependency report through this root. A test file not reachable here is not a
passing gate.
-/

#effect4_axiom_gate
