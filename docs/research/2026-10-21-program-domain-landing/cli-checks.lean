import ProofGraph.AxiomAudit
import ProofGraph.ClosureAudit
import Compiler.Main
import Test.Codegen.CompilerEmit
#axiom_audit Test.Codegen.CompilerEmit
#closure_audit Compiler.Check Compiler.Inspect Compiler.Main
