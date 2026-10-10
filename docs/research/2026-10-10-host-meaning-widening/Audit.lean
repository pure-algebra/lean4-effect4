import Meaning
import Controls
import BoundaryControls
import Goals
import ProofGraph.AxiomAudit
import ProofGraph.Plan

/-! Research-only trust and status receipts. The open H8 goal proves no control. -/
#axiom_audit Meaning Controls BoundaryControls Goals
#plan_status Test.HostMeaningWidening.h8_loopedRows

#eval [("paged stream", Test.HostMeaningWidening.Controls.agrees
          Test.HostMeaningWidening.Controls.collect Test.HostMeaningWidening.Controls.twoPages 4),
       ("host and request history", Test.HostMeaningWidening.Controls.h9Finite),
       ("budget cut", Test.HostMeaningWidening.Controls.budgetCut),
       ("waiting retains stores", Test.HostMeaningWidening.Controls.waitRetainsState),
       ("past answers do not stop a host", Test.HostMeaningWidening.Controls.prefixDoesNotStopHost),
       ("wrong request refused", Test.HostMeaningWidening.Controls.wrongRequestRejected)]
