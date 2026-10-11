import Effect4.Program.Eff
import Effect4.Program.Fold
import Effect4.Program.LayerView
import Effect4.Program.NodeLenses
import Effect4.Program.Scoped
import Effect4.Program.Authoring.Lifts
import Effect4.Program.Checker
import Effect4.Program.Compile
import Effect4.Program.Typing
import Effect4.Program.Typing.Annotate
import Effect4.Program.Typing.Focus
import Effect4.Store.Domain.Derived.Program
import Effect4.Codegen.PrintLeaf
import Effect4.Codegen.Templates
import Test.Program.FirstExitSource
import Effect4.Laws.Program.Authoring.Lifts
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Program.Eff Effect4.Program.Fold Effect4.Program.LayerView Effect4.Program.NodeLenses Effect4.Program.Scoped Effect4.Program.Authoring.Lifts Effect4.Program.Checker Effect4.Program.Compile Effect4.Program.Typing Effect4.Program.Typing.Annotate Effect4.Program.Typing.Focus Effect4.Store.Domain.Derived.Program Effect4.Codegen.PrintLeaf Effect4.Codegen.Templates Test.Program.FirstExitSource Effect4.Laws.Program.Authoring.Lifts
