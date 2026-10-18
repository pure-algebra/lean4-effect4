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

/-- A helper for restore_targets, consumed by the checked recovery connector. -/
theorem checkImageRoots_resolves {store : Store} {roots : List Root} {names : List String}
    (accepted : store.checkImageRoots names roots = .ok ()) :
    ∀ root ∈ roots, store.Resolves ⟨root.kind, root.head.digest⟩ := by
  induction roots generalizing names with
  | nil => intro root member; exact nomatch member
  | cons head rest ih =>
    change (show Except TxnRefusal Unit from if names.contains head.name then .error (.duplicateRoot head.name)
      else match store.checkEdge ⟨head.kind, head.head.digest⟩ with
        | .error why => .error (.target head.name why)
        | .ok () => store.checkImageRoots (head.name :: names) rest) = .ok () at accepted
    split at accepted
    · exact nomatch accepted
    · split at accepted
      · exact nomatch accepted
      · next checked =>
        intro root member
        cases member with
        | head => exact (checkEdge_ok_iff store _).mp checked
        | tail _ member => exact ih accepted root member

/-- Every checked root targets a durable admitted resident at its fixed kind. -/
@[semantics "translation-simulation" (requirement := R13)]
theorem restore_targets {image : RecoveryImage} {store : Store}
    (accepted : Store.empty.restore image = .ok store) :
    ∀ root ∈ store.roots, store.Resolves ⟨root.kind, root.head.digest⟩ := by
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
    · next checked =>
      injection accepted with same
      subst store
      intro root member
      change staged.Resolves ⟨root.kind, root.head.digest⟩
      exact checkImageRoots_resolves checked root member

end Effect4.Store
