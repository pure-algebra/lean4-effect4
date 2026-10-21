import Compiler.Main
import Compiler.Page
import Test.Codegen.CompilerEmit
import Tools.Document.Json
import ProofGraph.AxiomAudit
#axiom_audit Compiler.Inspect Compiler.InspectDocument Compiler.Main Compiler.Page Test.Codegen.CompilerEmit
#axiom_audit Tools.Document.Json
#axiom_audit ProofGraph.Registry
