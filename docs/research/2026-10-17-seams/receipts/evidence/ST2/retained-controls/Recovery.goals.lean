import Effect4.Store.Domain.Cas
import Effect4.Laws.Auto.Semantics

/-!
# Checked image recovery

Placement: `RESTORE-PLACEMENT.md`, translation-simulation, R13.
The compatibility question retains the exact checked root table.
The preservation question retains node closure through the shared admission.
Consumers: ST4 Exchange.load/apply and S6 reopened disk access.
Neither question reconstructs historical ancestry or generation provenance.
-/
namespace Effect4.Store

/-- Checked image admission retains each root record and generation exactly. -/
@[semantics "translation-simulation" (requirement := R13)]
proof_goal restore_roots {image : RecoveryImage} {store : Store}
    (accepted : Store.empty.restore image = .ok store) : store.roots = image.roots

/-- Checked image admission establishes node closure through the shared admission. -/
@[semantics "translation-simulation" (requirement := R13)]
proof_goal restore_closed {image : RecoveryImage} {store : Store}
    (accepted : Store.empty.restore image = .ok store) : Closed store

end Effect4.Store
