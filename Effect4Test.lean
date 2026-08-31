import Effect4Test.Algebra.ExtractionContract
import Effect4Test.Algebra.RetainedClosureContract
import Effect4Test.Algebra.AxiomReport
import Effect4Test.Flow.AdmissionContract
import Effect4Test.Flow.DiagnosticPrecisionContract
import Effect4Test.Flow.AxiomReport
import Effect4Test.Schema.AxiomReport
import Effect4Test.Flow.PrivacyContract
import Effect4Test.Counterexamples.Schema.CensusCoverage
import Effect4Test.Counterexamples.Schema.KindAlphabetSeparation
import Effect4Test.Counterexamples.Schema.NoLocalSymbolPropertyKey
import Effect4Test.Counterexamples.Schema.NoNullLiteralKind
import Effect4Test.Counterexamples.Schema.SemanticTagSeparation
import Effect4Test.Counterexamples.Schema.WireSpellingDrift
import Effect4Test.Schema.RepresentationContract
import Effect4Test.Schema.SubAlphabetContract
import Effect4Test.Schema.PayloadContract
import Effect4Test.Schema.PayloadSurface
import Effect4Test.Data.RowContract
import Effect4Test.Environment.ContextKeyContract
import Effect4Test.Environment.AxiomReport
import Effect4Test.Audit.AxiomGate

/-!
# Effect4 test battery

The default Lake build imports every admitted contract, attack, and kernel
dependency report through this root. A test file not reachable here is not a
passing gate.
-/

#effect4_axiom_gate
