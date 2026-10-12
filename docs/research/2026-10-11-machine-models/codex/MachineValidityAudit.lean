import Effect4.Laws.Machine.StoreValidity
import Effect4.Laws.Store.Names
import Effect4.Laws.Machine.StoresLaws
import Effect4.Laws.Machine.Handles
import Effect4.Laws.Machine.StoresValue
import Test.Machine.Runtime.StoresLawsContract
import ProofGraph.AxiomAudit

#axiom_audit Effect4.Laws.Machine.StoreValidity Effect4.Laws.Store.Names Effect4.Laws.Machine.StoresLaws Effect4.Laws.Machine.Handles Effect4.Laws.Machine.StoresValue Test.Machine.Runtime.StoresLawsContract
