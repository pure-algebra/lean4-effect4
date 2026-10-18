import Effect4.Laws.Store.Recovery
import Test.Store.SeamsTransactions

/-!
# Test.Store.SeamsRecovery — checked recovery from a disk image (seams ST2)

Finite controls of `Cas.restore` and `Cas.restoreBytes`. A legacy root at generation two restores
with its exact head. A nonempty store, a duplicate root, a dangling or wrong-kind target, an unknown
tag and a bad version each refuse, with the address or the index that names the fault. The laws are
`restore_roots`, `restore_closed` and `restore_targets` in `Laws/Store/Recovery.lean`.
-/
set_option autoImplicit false
namespace Test.Store.SeamsRecovery
open Effect4.Store
open Test.Store.SeamsTransactions

def legacyRoot : Root := ⟨"docs/a", .swap, .«export», ⟨probeEntryAddress, 2⟩⟩
def legacy : RecoveryImage := ⟨[probeSchema, probeEntry], [legacyRoot]⟩
#guard match Cas.restore legacy with
  | .ok cas => cas.store.roots = [legacyRoot] ∧ cas.store.nodes = initial.nodes
  | _ => false
#guard match Cas.restoreBytes [probeSchema.encode, probeEntry.encode] [legacyRoot] with
  | .ok cas => (cas.store.root? "docs/a").map Root.head = some ⟨probeEntryAddress, 2⟩
  | _ => false
#guard match rooted.restore legacy with
  | .error .restoreNonempty => true
  | _ => false
#guard match Store.empty.restore ⟨legacy.nodes, [legacyRoot, legacyRoot]⟩ with
  | .error (.duplicateRoot "docs/a") => true
  | _ => false
#guard match Store.empty.restore ⟨[probeSchema], [legacyRoot]⟩ with
  | .error (.target "docs/a" (.dangling digest)) => digest = probeEntryAddress
  | _ => false
#guard match Store.empty.restore ⟨legacy.nodes, [{legacyRoot with kind := .schema}]⟩ with
  | .error (.target "docs/a" (.wrongKind digest .schema .«export»)) => digest = probeEntryAddress
  | _ => false

def unknown : Bytes := [0, Kind.export.byte] ++ zeroDigest.bytes ++ framed 253 []
#guard match Cas.restoreBytes [unknown] [] with
  | .error (.node 0 (.unknownTag 253)) => true
  | _ => false
#guard match Cas.empty.commitBytes [unknown] [] with
  | .error (.node 0 (.unknownTag 253)) => true
  | _ => false
#guard match Cas.empty.commitBytes [1 :: unknown.drop 1] [] with
  | .error (.node 0 .badVersion) => true
  | _ => false

example {next : Store} (accepted : Store.empty.restore legacy = .ok next) :
    next.roots = [legacyRoot] := restore_roots accepted
example {next : Store} (accepted : Store.empty.restore legacy = .ok next) :
    Closed next := restore_closed accepted
example {next : Store} (accepted : Store.empty.restore legacy = .ok next) :
    next.Resolves ⟨legacyRoot.kind, legacyRoot.head.digest⟩ :=
  restore_targets accepted legacyRoot (by
    rw [restore_roots accepted]
    exact List.mem_cons_self)
end Test.Store.SeamsRecovery
