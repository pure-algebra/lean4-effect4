import Test.Schema.AxiomReport
import Test.Data.OpticContract
import Test.Schema.AnnotationDataPlaneContract
import Test.Schema.EffectfulFieldContract
import Test.Schema.EffectfulFieldPropertiesContract
import Test.Schema.AuthoringContract
import Test.Counterexamples.Codegen.TypeScriptRender
import Test.Counterexamples.Schema.CensusCoverage
import Test.Counterexamples.Schema.KindAlphabetSeparation
import Test.Counterexamples.Schema.NoLocalSymbolPropertyKey
import Test.Counterexamples.Schema.NoNullLiteralKind
import Test.Counterexamples.Schema.SemanticTagSeparation
import Test.Counterexamples.Schema.WireSpellingDrift
import Test.Counterexamples.Schema.AnnotationDataPlane
import Test.Counterexamples.Schema.EffectfulField
import Test.Counterexamples.Schema.EffectfulFieldProperties
import Test.Counterexamples.Schema.RecursiveElimination
import Test.Schema.RepresentationContract
import Test.Schema.RepresentationFoldContract
import Test.Schema.SubAlphabetContract
import Test.Schema.PayloadContract
import Test.Schema.PayloadSurface
import Test.Schema.StructuralAssurance
import Test.Data.RowContract
import Test.Data.RowAssurance
import Test.Data.AxiomReport
import Test.Machine.Environment.ContextKeyContract
import Test.Machine.Environment.AxiomReport
import Test.Machine.Environment.ContextKeyAssurance
import Test.Codegen.ExprContract
import Test.Codegen.SchemaGenerationContract
import Test.Codegen.SchemaGenerationCoverage
import Test.Codegen.SchemaGenerationAxiomReport
import Test.Codegen.EffectfulFieldContract
import Test.Codegen.EffectfulFieldAxiomReport
import Test.Counterexamples.Codegen.EffectfulField
import Test.Machine.Semantics.CauseExitContract
import Test.Machine.Semantics.CauseExitAxiomReport
import Test.Counterexamples.Machine.Semantics.CauseExit
import Test.Machine.Runtime.ScopeContract
import Test.Machine.Runtime.ScopeAxiomReport
import Test.Machine.Runtime.ScopeMachineContract
import Test.Machine.Runtime.ScopeMachineAxiomReport
import Test.Machine.Runtime.ScopeRestorationContract
import Test.Machine.Runtime.ScopeRestorationAxiomReport
import Test.Counterexamples.Machine.Runtime.ScopeRestorationBoundary
import Test.Counterexamples.Machine.Runtime.Scope
import Test.Machine.Runtime.FramesContract
import Test.Machine.Runtime.FramesAxiomReport
import Test.Counterexamples.Machine.Runtime.Frames
import Test.Machine.Runtime.LiveStackContract
import Test.Machine.Runtime.LiveStackAxiomReport
import Test.Counterexamples.Machine.Runtime.LiveStack
import Test.Store.StoreContract
import Test.Evidence.ArchContract
import Test.Codegen.PrintContract
import Test.Codegen.RuleContract
import Test.Codegen.AppContract
import Test.Ingest.JsonSchemaContract
import Test.Ingest.WranglerContract
import Test.Ingest.McpContract
import Test.Program.CompileContract
import Test.Api.ApiContract
import Test.Machine.Fuzz
import Test.Audit.RuntimeCoverage
import Test.Audit.AxiomGate

/-!
# Effect4 test battery

The default Lake build imports every admitted contract, attack, and kernel
dependency report through this root. A test file not reachable here is not a
passing gate. The batteries of the Flow route live on branch
`archive/flow-route` (`docs/research/2026-09-04-prod-cleanup-inventory.md`).
-/

#effect4_axiom_gate
