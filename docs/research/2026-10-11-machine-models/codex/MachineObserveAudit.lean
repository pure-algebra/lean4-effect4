import Effect4.Laws.Machine.Edits
import Effect4.Laws.Machine.EditWords
import Effect4.Laws.Machine.Ledger
import Effect4.Laws.Machine.FiberSumMessages
import Effect4.Laws.Machine.Handles
import Effect4.Laws.Machine.Clauses
import Test.Machine.EditFields
import Test.Machine.EditMessages
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.ReturnFields
import Effect4.Laws.Program.Guard.NativeState
import Effect4.Laws.Program.Guard.Observer
import Effect4.Laws.Program.Guard.SettleQueue
import Effect4.Laws.Program.Typed.Commands.Bookkeeping
import Effect4.Laws.Program.Typed.Commands.Observe
import Effect4.Laws.Program.Typed.Commands.Clauses.Park
import Effect4.Laws.Program.Typed.Commands.Clauses.Command
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Machine.Fibers Effect4.Laws.Machine.Edit Effect4.Laws.Machine.Keeps Effect4.Laws.Machine.Edits Effect4.Laws.Machine.Clauses Effect4.Laws.Machine.Ledger Effect4.Laws.Machine.FiberSumMessages Effect4.Laws.Machine.Handles Effect4.Laws.Program.Guard.Core Effect4.Laws.Program.Guard.ReturnFields Effect4.Laws.Program.Guard.NativeState Test.Machine.EditFields Test.Machine.EditMessages Effect4.Laws.Program.Guard.Observer Effect4.Laws.Program.Guard.SettleQueue Effect4.Laws.Program.Typed.Commands.Bookkeeping Effect4.Laws.Program.Typed.Commands.Observe Effect4.Laws.Program.Typed.Commands.Clauses.Park Effect4.Laws.Program.Typed.Commands.Clauses.Command
