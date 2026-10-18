import Effect4.Store.Domain.Cas

set_option autoImplicit false
namespace Test.Store.SeamsTransactions
open Effect4.Store

def accepted (result : Except TxnRefusal (Receipt × Store)) : Store :=
  match result with | .ok (_, store) => store | .error _ => Store.empty

def pairTxn : Txn := ⟨[probeSchema, probeEntry], []⟩
def initial : Store := accepted (Store.empty.commit pairTxn)
#guard match Store.empty.commit pairTxn with
  | .ok (receipt, _) => receipt.nodes = [(probeSchemaAddress, .fresh), (probeEntryAddress, .fresh)]
  | _ => false
#guard match initial.commit ⟨[probeEntry], []⟩ with
  | .ok (receipt, _) => receipt.nodes = [(probeEntryAddress, .duplicate)]
  | _ => false

def create : Txn := ⟨[], [.create "docs/a" .swap ⟨.«export», probeEntryAddress⟩]⟩
def rooted : Store := accepted (initial.commit create)
#guard match initial.commit create with
  | .ok (receipt, store) => receipt.moves = [.created 1] ∧
      (store.root? "docs/a").map Root.head = some ⟨probeEntryAddress, 1⟩
  | _ => false
#guard match rooted.commit create with
  | .error (.staleRoot "docs/a" none (some head)) => head = ⟨probeEntryAddress, 1⟩
  | _ => false
#guard match rooted.commit ⟨[], [.advance "docs/a" ⟨probeEntryAddress, 1⟩ ⟨.«export», probeEntryAddress⟩]⟩ with
  | .ok (receipt, _) => receipt.moves = [.duplicate 1]
  | _ => false
#guard match rooted.commit ⟨[], [.advance "docs/a" ⟨probeSchemaAddress, 1⟩ ⟨.«export», probeSchemaAddress⟩]⟩ with
  | .error (.staleRoot "docs/a" _ _) => true
  | _ => false

def alternate : Node := {probeEntry with payload := .str "alternate"}
def alternateAddress : Digest := sha256 alternate.encode

def aba : Txn := ⟨[alternate],
  [.advance "docs/a" ⟨probeEntryAddress, 1⟩ ⟨.«export», alternateAddress⟩,
   .advance "docs/a" ⟨alternateAddress, 2⟩ ⟨.«export», probeEntryAddress⟩]⟩
def afterABA : Store := accepted (rooted.commit aba)
#guard match rooted.commit aba with
  | .ok (receipt, store) => receipt.moves = [.advanced 2, .advanced 3] ∧
      (store.root? "docs/a").map Root.head = some ⟨probeEntryAddress, 3⟩
  | _ => false
#guard match afterABA.commit ⟨[], [.advance "docs/a" ⟨probeEntryAddress, 1⟩ ⟨.«export», alternateAddress⟩]⟩ with
  | .error (.staleRoot "docs/a" _ _) => true
  | _ => false

def pinned : Store := accepted (initial.commit ⟨[], [.create "pin/a" .pin ⟨.«export», probeEntryAddress⟩]⟩)
#guard match pinned.commit ⟨[], [.advance "pin/a" ⟨probeEntryAddress, 1⟩ ⟨.«export», probeEntryAddress⟩]⟩ with
  | .ok (receipt, _) => receipt.moves = [.duplicate 1]
  | _ => false
#guard match pinned.commit ⟨[alternate], [.advance "pin/a" ⟨probeEntryAddress, 1⟩ ⟨.«export», alternateAddress⟩]⟩ with
  | .error (.pinned "pin/a") => true
  | _ => false

def t : Node := {probeEntry with payload := .str "T"}
def td : Digest := sha256 t.encode
def u : Node := {probeEntry with payload := .ref Kind.«export».byte td.bytes}
def ud : Digest := sha256 u.encode
def prefixTxn : Txn := ⟨[probeEntry, t, u], [.advance "docs/a" ⟨probeEntryAddress, 1⟩ ⟨.«export», ud⟩]⟩
#guard match rooted.interrupted prefixTxn (.nodes 1) with
  | .ok store => store.find probeEntryAddress = some probeEntry ∧ store.find td = some t ∧
      store.find ud = none ∧ store.roots = rooted.roots
  | _ => false
#guard match rooted.interrupted prefixTxn .published, rooted.commit prefixTxn with
  | .ok interrupted, .ok (_, committed) => interrupted.nodes = committed.nodes ∧ interrupted.roots = committed.roots
  | _, _ => false
#guard match rooted.interrupted prefixTxn (.nodes 0) with
  | .ok store => store.nodes = rooted.nodes ∧ store.roots = rooted.roots
  | _ => false
#guard match rooted.interrupted prefixTxn (.nodes 100) with
  | .ok store => store.find td = some t ∧ store.find ud = some u ∧ store.roots = rooted.roots
  | _ => false

def lateBad : Txn := {prefixTxn with moves := prefixTxn.moves ++ [.advance "absent" ⟨ud, 1⟩ ⟨.«export», ud⟩]}
#guard match rooted.commit lateBad with | .error (.noRoot "absent") => true | _ => false
#guard match rooted.interrupted lateBad (.nodes 1) with | .error (.noRoot "absent") => true | _ => false
#guard match rooted.interrupted lateBad .published with | .error (.noRoot "absent") => true | _ => false

-- Designated parents are distinct from incidental payload references.
def origin : Node := ⟨0, .entry, probeSchemaAddress, .ctor 0 [.nat 1, .nat 1, .str "engine"]⟩
def originAddress : Digest := sha256 origin.encode
def entry (parent : Digest) (action : Val) : Node :=
  ⟨0, .entry, probeSchemaAddress, .ctor 1 [.ref Kind.entry.byte parent.bytes, .nat 0, action, .none]⟩
def child : Node := entry originAddress (.str "act")
def childAddress : Digest := sha256 child.encode
def incidental : Node := ⟨0, .entry, probeSchemaAddress,
  .ctor 0 [.ref Kind.entry.byte originAddress.bytes, .nat 1, .str "origin"]⟩
def incidentalAddress : Digest := sha256 incidental.encode
def journalBase : Store := accepted (initial.commit ⟨[origin], [.create "session/a" .journal ⟨.entry, originAddress⟩]⟩)
#guard match journalBase.commit ⟨[child], [.advance "session/a" ⟨originAddress, 1⟩ ⟨.entry, childAddress⟩]⟩ with
  | .ok (receipt, _) => receipt.moves = [.advanced 2]
  | _ => false
#guard match journalBase.commit ⟨[incidental], [.advance "session/a" ⟨originAddress, 1⟩ ⟨.entry, incidentalAddress⟩]⟩ with
  | .error (.fork "session/a" head target) => head = originAddress ∧ target = incidentalAddress
  | _ => false
#guard match journalBase.commit ⟨[child], [.create "session/fork" .journal ⟨.entry, childAddress⟩]⟩ with
  | .ok (_, store) => (store.root? "session/a").map Root.head = some ⟨originAddress, 1⟩ ∧
      (store.root? "session/fork").map Root.head = some ⟨childAddress, 1⟩
  | _ => false
#guard match replayEvents [.commit pairTxn, .commit create, .interrupt prefixTxn (.nodes 1)] with
  | .ok store => store.find td = some t ∧ store.find ud = none ∧ store.roots = rooted.roots
  | _ => false
-- An absent advance refuses before target resolution.
#guard match initial.commit ⟨[], [.advance "missing" ⟨zeroDigest, 0⟩ ⟨.schema, zeroDigest⟩]⟩ with
  | .error (.noRoot "missing") => true
  | _ => false
-- Wrong-kind targets cannot become duplicates through a matching digest.
#guard match rooted.commit ⟨[], [.advance "docs/a" ⟨probeEntryAddress, 1⟩ ⟨.schema, probeEntryAddress⟩]⟩ with
  | .error (.target "docs/a" (.wrongKind _ .«export» .schema)) => true
  | _ => false
-- Stale pin expectations precede pinned refusal.
#guard match pinned.commit ⟨[], [.advance "pin/a" ⟨probeEntryAddress, 0⟩ ⟨.schema, zeroDigest⟩]⟩ with
  | .error (.staleRoot "pin/a" _ _) => true
  | _ => false
-- Existing duplicate nodes consume no cut count, including a run of duplicates.
#guard match rooted.interrupted ⟨[probeSchema, probeEntry, t, u], []⟩ (.nodes 1) with
  | .ok store => store.find td = some t ∧ store.find ud = none
  | _ => false
-- A transaction fails at its actual node index and returns no prefix receipt.
#guard match initial.commit ⟨[probeEntry, ⟨1, .schema, zeroDigest, .nat 0⟩], []⟩ with
  | .error (.node 1 .badVersion) => true
  | _ => false
-- A collision is a transaction refusal, even when the put primitive reports an outcome.
def collisionStore : Store := ⟨[(probeSchemaAddress, probeSchema),
  (probeEntryAddress, {probeEntry with payload := .nat 3})], []⟩
#guard match collisionStore.commit ⟨[probeEntry], []⟩ with
  | .error (.node 0 (.conflict address occupant)) => address = probeEntryAddress ∧ occupant.payload = .nat 3
  | _ => false
-- A successful prior root move does not hide a later failure.
#guard match initial.commit ⟨[], [.create "temporary" .swap ⟨.«export», probeEntryAddress⟩,
    .advance "absent" ⟨zeroDigest, 0⟩ ⟨.schema, zeroDigest⟩]⟩ with
  | .error (.noRoot "absent") => initial.root? "temporary" = none
  | _ => false
-- Empty transactions and cuts retain the exact preexisting node list.
#guard match rooted.interrupted ⟨[], []⟩ (.nodes 100) with
  | .ok store => store.nodes = rooted.nodes ∧ store.roots = rooted.roots
  | _ => false
-- Names compare exactly; case never aliases another root.
#guard match rooted.commit ⟨[], [.create "Docs/a" .pin ⟨.schema, probeSchemaAddress⟩]⟩ with
  | .ok (_, store) => (store.root? "docs/a").map Root.head = some ⟨probeEntryAddress, 1⟩ ∧
      (store.root? "Docs/a").map Root.head = some ⟨probeSchemaAddress, 1⟩
  | _ => false

-- Checkpoints designate only their fourth canonical field as parent.
def checkpointParent : Node := ⟨0, .checkpoint, probeSchemaAddress,
  .ctor 0 [.nat 0, .nat 0, .none, .none, .bytes zeroDigest.bytes, .nat 0, .nat 0]⟩
def checkpointParentAddress : Digest := sha256 checkpointParent.encode
def checkpointChild : Node := {checkpointParent with payload := .ctor 0 [.nat 0, .nat 1, .none,
    .some (.ref Kind.checkpoint.byte checkpointParentAddress.bytes),
    .bytes zeroDigest.bytes, .nat 0, .nat 0]}
#guard checkpointChild.designatedParent = some checkpointParentAddress
#guard ({checkpointParent with payload := .ctor 0 [
  .ref Kind.checkpoint.byte checkpointParentAddress.bytes, .nat 0, .none, .none,
  .bytes zeroDigest.bytes, .nat 0, .nat 0]} : Node).designatedParent = none
end Test.Store.SeamsTransactions
