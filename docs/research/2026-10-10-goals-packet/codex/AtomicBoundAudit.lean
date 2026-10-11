import Test.Dogfood.Scenario.NativeHeap
import Test.Dogfood.Scenario.SourceFragment
import Test.Dogfood.Scenario.Atomic
import Effect4.Laws.Program.ReleaseCustody.Execution
import ProofGraph.AxiomAudit
#axiom_audit Effect4.Laws.Program.CompileInduction Effect4.Laws.Program.SourceOrigin Effect4.Laws.Program.ScopeFragment Effect4.Laws.Program.NativeScope Effect4.Laws.Program.NativeStoreScope Effect4.Laws.Program.NativeCallbacks Effect4.Laws.Program.NativeInterpScope Effect4.Laws.Program.NativeFrameScope Effect4.Laws.Program.NativeActionScope Effect4.Laws.Program.NativeScopeStore Effect4.Laws.Program.HeapSites.Core Effect4.Laws.Program.NativeHeap Effect4.Laws.Program.NativeConfiguration Effect4.Laws.Program.NativeEvaluation Effect4.Laws.Program.NativeActions Effect4.Laws.Program.NativeExecutor Effect4.Laws.Program.NativeCommands Effect4.Laws.Program.NativeHistory Test.Dogfood.Scenario.SourceFragment Effect4.Laws.Program.NativeReferences Effect4.Laws.Program.NativeHeapExecution Effect4.Laws.Program.NativeHeapHistory Effect4.Laws.Program.HeapSites Test.Dogfood.Scenario.NativeHeap

#axiom_audit Test.Dogfood.Scenario.Atomic Effect4.Laws.Program.ReleaseCustody.FrameDebit
#plan_status Test.Dogfood.Scenario.Atomic.bounded Test.Dogfood.Scenario.Atomic.counted Test.Dogfood.Scenario.Atomic.committed Test.Dogfood.Scenario.Atomic.cleans_once
