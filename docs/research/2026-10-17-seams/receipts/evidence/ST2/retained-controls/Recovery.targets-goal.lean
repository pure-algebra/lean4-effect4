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
theorem restore_roots {image : RecoveryImage} {store : Store}
    (accepted : Store.empty.restore image = .ok store) : store.roots = image.roots := by
  change (show Except TxnRefusal Store from match Store.empty.stageNodes 0 image.nodes with
    | .error why => .error why
    | .ok (_, staged, _) => match staged.checkImageRoots [] image.roots with
      | .error why => .error why
      | .ok () => .ok {staged with roots := image.roots}) = .ok store at accepted
  split at accepted
  · exact nomatch accepted
  · next outcomes staged prefixes prepared =>
    split at accepted
    · exact nomatch accepted
    · injection accepted with same
      subst store
      rfl

/-- Checked image admission establishes node closure through the shared admission. -/
@[semantics "translation-simulation" (requirement := R13)]
theorem restore_closed {image : RecoveryImage} {store : Store}
    (accepted : Store.empty.restore image = .ok store) : Closed store := by
  change (show Except TxnRefusal Store from match Store.empty.stageNodes 0 image.nodes with
    | .error why => .error why
    | .ok (_, staged, _) => match staged.checkImageRoots [] image.roots with
      | .error why => .error why
      | .ok () => .ok {staged with roots := image.roots}) = .ok store at accepted
  split at accepted
  · exact nomatch accepted
  · next outcomes staged prefixes prepared =>
    split at accepted
    · exact nomatch accepted
    · injection accepted with same
      subst store
      exact closed_of_nodes_eq rfl (stageNodes_closed empty_closed prepared).1

/-- Every checked root targets a durable admitted resident at its fixed kind. -/
@[semantics "translation-simulation" (requirement := R13)]
proof_goal restore_targets {image : RecoveryImage} {store : Store}
    (accepted : Store.empty.restore image = .ok store) :
    ∀ root ∈ store.roots, store.Resolves ⟨root.kind, root.head.digest⟩

end Effect4.Store
