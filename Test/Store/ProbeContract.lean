/-
Contract: the spike's probe battery, kept whole (`Test/Store/ProbeContract.lean`).

Frozen: what the spike guarded that the node, word and trait contracts beside this file do not
— the store in which the facts note's §6 stand-in spec resolves, and `p42` as a program node.

Why a hand-seeded store. The §6 illustrations address the census entry under
`6a1c…cac8`, the address today's JSON-route `entryDoc` had; no node hashes to that number, so a
store that admits the entry under it has to be written by hand. That is exactly what the
seeded store below is, and `verify` says so: it refuses with `digestMismatch 6a1c…`, which is
the receipt that the number is a stand-in and not an address of this store. The entry's real
node, under the real spec `268ee1…aa7c`, is `Test/Store/NodeContract.lean`'s.

`p42` is the other half: a `program` node with the zero spec, which every store refuses as
`dangling zeroDigest` because only the genesis carries that spec. Its address `8032…c13a` is
the number the facts note fixed for it, and its 66 payload bytes are the Wire's, unchanged by
the landing.

Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Store.Word
import Effect4.Program.Wire
import Test.Store.NodeContract

namespace Test.Store.ProbeContract

open Effect4.Store
open Test.Store.NodeContract (entrySpec entryNode entryAddress entryTwin)

/-! ## The seeded store: `fresh`, `duplicate`, `dangling`, `wrongKind` under a stand-in spec -/

/-- A stand-in schema node seeded under the facts note's `entryDoc` address. The key is not the
node's hash — the number comes from the retired store — and `verify` says so. -/
def seededSpec : Node := ⟨0, .schema, zeroDigest, .str "entryDoc"⟩

/-- The seeded store: the stand-in under the spec key, nothing else. -/
def seeded : Store := ⟨[(entrySpec, seededSpec)], []⟩

-- The entry enters fresh at the facts note's address, and is found there.
#guard outcomeIs (seeded.putNode entryNode) .fresh
#guard (match seeded.putNode entryNode with
  | .ok (.fresh, d, s) => d = entryAddress && s.find entryAddress = some entryNode
  | _ => false)
-- The same node again is a duplicate and the store does not grow.
#guard outcomeIs ((afterPut seeded entryNode).putNode entryNode) .duplicate
#guard (afterPut (afterPut seeded entryNode) entryNode).nodes.length = 2
-- The kind-6 twin is a different address, so it enters fresh beside it.
#guard outcomeIs ((afterPut seeded entryNode).putNode entryTwin) .fresh
#guard (afterPut (afterPut seeded entryNode) entryTwin).nodes.length = 3
#guard (afterPut (afterPut seeded entryNode) entryTwin).find (sha256 entryTwin.encode) =
  some entryTwin

-- The spec edge is resolved by address and kind, not by the payload's type: any kind of node
-- may cite a resident schema node.
#guard outcomeIs
  (seeded.putNode ⟨0, .program, entrySpec, Canonical.toVal Effect4.Program.Wire.Corpus.p42⟩)
  .fresh

-- Without the seed the entry dangles at its spec.
#guard refusedWith (Store.empty.putNode entryNode) (.dangling entrySpec)
-- The spec key held by a node of the wrong kind refuses before anything is written.
#guard refusedWith
  ((Store.mk [(entrySpec, ⟨0, .tree, zeroDigest, .list []⟩)] []).putNode entryNode)
  (.wrongKind entrySpec .schema .tree)
-- A typed reference into the store must resolve at its own kind.
#guard refusedWith ((afterPut seeded entryNode).putNode
    ⟨0, .tree, entrySpec, .ref 6 entryAddress.bytes⟩)
  (.wrongKind entryAddress .annotation .«export»)
#guard outcomeIs ((afterPut seeded entryNode).putNode
  ⟨0, .tree, entrySpec, .ref 2 entryAddress.bytes⟩) .fresh

-- A hand-seeded store is not a sound one: the seed is not filed at the hash of its bytes.
#guard (match seeded.verify with
  | .error (.digestMismatch d) => d = entrySpec
  | _ => false)
#guard (match (Store.mk [(entrySpec, seededSpec), (entryAddress, entryNode)] []).verify with
  | .error (.digestMismatch d) => d = entrySpec
  | _ => false)

/-! ## `p42` as a program node -/

/-- `p42` at kind 5 with the zero spec: the facts note's program illustration. -/
def p42Node : Node :=
  ⟨0, .program, zeroDigest, Canonical.toVal Effect4.Program.Wire.Corpus.p42⟩

-- The payload is the Wire's 66 bytes with the digest `digestOf p42` used to answer before the
-- landing.
#guard (Canonical.encode Effect4.Program.Wire.Corpus.p42).length = 66
#guard (Canonical.digest Effect4.Program.Wire.Corpus.p42).hex =
  "fa5f40f054198e91b2446522308e197b0a02c4edfe823f894763d3aa63ad62a3"
#guard p42Node.encode.length = 34 + 66
#guard (sha256 p42Node.encode).hex =
  "8032405e589e111c77c13b95b8a2ea408627f4e855ee3e8891fb3ac51676c13a"
#guard Node.decode p42Node.encode = some p42Node
-- Only the genesis carries the zero spec, so no store admits this node as it stands.
#guard refusedWith (Store.empty.putNode p42Node) (.dangling zeroDigest)
#guard refusedWith (seeded.putNode p42Node) (.dangling zeroDigest)

/-! ## The substrate's own fixture agrees with the templates -/

#guard probeEntry = ⟨0, .«export», probeSchemaAddress, Canonical.toVal Templates.entry⟩
#guard probeEntry.payload = sampleEntry

/-! ## Axiom receipts -/

#print axioms Effect4.Store.outcomeIs
#print axioms Effect4.Store.refusedWith
#print axioms Effect4.Store.afterPut
#print axioms Effect4.Store.probeSchema
#print axioms Effect4.Store.probeEntry
#print axioms Effect4.Store.probeStore
#print axioms Effect4.Store.probeWord
#print axioms Effect4.Store.probeLocal
#print axioms seededSpec
#print axioms seeded
#print axioms p42Node

end Test.Store.ProbeContract
