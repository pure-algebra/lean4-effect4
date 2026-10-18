import Effect4.Store.Domain.Word

/-!
Finite controls for seams review Q5 and Q6 at 774ddc3d7.
Consumer: the review of README sections 5.1, 5.3 and 5.4.
These evaluations use the existing store. They prove no proposed Cas invariant.
The coordinator runs this file through scratch/lean-slot.sh.
-/

set_option maxRecDepth 4096

open Effect4.Store

namespace SeamsStoreControls

/-! A result index over resident nodes needs an admission rule beyond putNode.
Two result nodes can name one query. Node admission accepts both.
The proposed transaction must close this path even when moves is empty.
-/

def query : Node := ⟨0, .query, probeSchemaAddress, .nat 0⟩
def queryAddress : Digest := sha256 query.encode
def result0 : Node :=
  ⟨0, .result, probeSchemaAddress, .ctor 0 [.ref 8 queryAddress.bytes, .nat 0]⟩
def result1 : Node :=
  ⟨0, .result, probeSchemaAddress, .ctor 0 [.ref 8 queryAddress.bytes, .nat 1]⟩
def withQuery : Store := afterPut probeStore query
def withResult0 : Store := afterPut withQuery result0
def withBothResults : Store := afterPut withResult0 result1

#guard outcomeIs (withQuery.putNode result0) .fresh
#guard outcomeIs (withResult0.putNode result1) .fresh
#guard result0.refsOf = [⟨.query, queryAddress⟩]
#guard result1.refsOf = [⟨.query, queryAddress⟩]
#guard (withBothResults.nodes.filter (fun p => p.2.kind == .result)).length = 2

/-! The current version check rejects a stale move after a root returns to A.
Digest equality alone sees the same A before and after A, B, A.
This control concerns swap roots. An actual history policy adds another premise.
-/

def otherEntry : Node := ⟨0, .«export», probeSchemaAddress, .nat 7⟩
def otherAddress : Digest := sha256 otherEntry.encode
def bothTargets : Store := afterPut probeStore otherEntry
def rootA1 : Root := ⟨"swap/a", .stdlib, .«export», probeEntryAddress, 1⟩
def rootB2 : Root := ⟨"swap/a", .stdlib, .«export», otherAddress, 2⟩
def rootA3 : Root := ⟨"swap/a", .stdlib, .«export», probeEntryAddress, 3⟩
def atA1 : Store := putRootOr bothTargets rootA1
def atB2 : Store := putRootOr atA1 rootB2
def atA3 : Store := putRootOr atB2 rootA3

#guard (atA1.root? "swap/a").map Root.digest =
  (atA3.root? "swap/a").map Root.digest
#guard (atA1.root? "swap/a").map Root.version = some 1
#guard (atA3.root? "swap/a").map Root.version = some 3
#guard match atA3.putRoot rootB2 with
  | .error (.staleRoot "swap/a" 4 2) => true
  | _ => false

/-! In worked row 5 the target is independently wrong-kind.
The current root check reports staleness first, then wrong-kind with a fresh version.
-/

#guard match atA1.putRoot ⟨"swap/a", .stdlib, .«export», probeSchemaAddress, 1⟩ with
  | .error (.staleRoot "swap/a" 2 1) => true
  | _ => false
#guard match atA1.putRoot ⟨"swap/a", .stdlib, .«export», probeSchemaAddress, 2⟩ with
  | .error (.wrongKind _ .«export» .schema) => true
  | _ => false

/-! A resident node does not bypass admission. A missing spec beats duplicate.
This bounds a retry-idempotence claim to reachable stores and unchanged policies.
-/

def unclosedResident : Store := ⟨[(probeEntryAddress, probeEntry)], []⟩
#guard refusedWith (unclosedResident.putNode probeEntry) (.dangling probeSchemaAddress)

/-! The proposed state image carries a document and run references.
Those edges contain no old state image. A direct-edge journal policy needs an added link.
-/

def state0 : Node :=
  ⟨0, .tree, probeSchemaAddress,
    .ctor 0 [.list [.pair (.str "doc") (.ref 2 probeEntryAddress.bytes)]]⟩
def state1 : Node :=
  ⟨0, .tree, probeSchemaAddress,
    .ctor 0 [.list [.pair (.str "doc") (.ref 2 otherAddress.bytes)]]⟩
#guard state0.refsOf = [⟨.«export», probeEntryAddress⟩]
#guard state1.refsOf = [⟨.«export», otherAddress⟩]
#guard !(state1.refsOf.any (fun e => e.kind == .tree))

end SeamsStoreControls
