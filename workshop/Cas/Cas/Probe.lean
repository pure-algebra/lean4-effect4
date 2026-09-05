import Cas.Traits
import Cas.Templates
import Cas.Program

/-!
# Cas.Probe

The battery of the spike (`docs/research/2026-09-04-cas-trait-plan.md` §7, `NodeContract`,
`WordContract`, `TraitContract`) run inside the workshop against the facts note's §6 numbers.

The entry is S1's `Templates.entry` through its instance (its value tree is `sampleEntry`, its
payload digest `8fab16…61fa`); the spec is today's `entryDoc` address
`6a1c902ee204a7856387132a13975908fd4d891c7cc1a55e3179ddaf5e01cac8`, the stand-in the facts note
used, given explicitly because `Canonical Document` does not exist until lane G derives it. Under
that spec the entry's node is 108 bytes at address `1437a1…705b` (a `Ref Entry`), the same payload
filed at kind 6 is `ca0785…0990`, and `p42` from S1's `Cas.Program` at kind 5 with the zero spec is
`8032…c13a`. The typed reference frame to the entry node is the 42-byte `0b …21 02 1437…`.

The store half needs a store in which the stand-in spec resolves. No node hashes to `6a1c…`
(it is an address of the old store), so the spec is seeded by hand under that key — a store
`verify` refuses as `digestMismatch 6a1c…`, which is guarded too. In it the entry enters `fresh`
at `1437…`, again as `duplicate`, and the twin `fresh` at `ca07…`; in the empty store both the
entry and the zero-spec `p42` node are `dangling`; a `tree` seed under the spec key is
`wrongKind`. The word, closure, layered, outbox, verify and trait guards run on the genuine
world of `Cas.Store`/`Cas.Word`/`Cas.Traits` (the stand-in genesis and the same entry under its
real address), restated here in the order the brief lists them.
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Document)

/-! ## The entry node, its twin, `p42`, and the typed reference (facts note §6) -/

/-- Today's `entryDoc` address: the explicit spec of the probe. -/
def entrySpecHex : String := "6a1c902ee204a7856387132a13975908fd4d891c7cc1a55e3179ddaf5e01cac8"

/-- The spec as a digest. -/
def entrySpec : Digest := (Digest.ofHex? entrySpecHex).getD zeroDigest

#guard (Digest.ofHex? entrySpecHex).isSome
#guard entrySpec.hex = entrySpecHex

/-- The entry node: `00 │ 02 │ spec (32) │ payload (74)`, 108 bytes. -/
def entryNode : Node := ⟨0, .«export», entrySpec, Canonical.toVal Templates.entry⟩

/-- Its address, the facts note's `Ref Entry`. -/
def entryAddress : Digest := sha256 entryNode.encode

#guard Canonical.toVal Templates.entry = sampleEntry
#guard entryNode.encode.length = 108
#guard entryNode.encode.take 2 = [0x00, 0x02]
#guard (entryNode.encode.drop 2).take 32 = entrySpec.bytes
#guard entryNode.encode.drop 34 = Val.encode sampleEntry
#guard (sha256 (Val.encode sampleEntry)).hex =
  "8fab161870afe7d35c681679cf5dced52845b5ebef2b84b6c85e4b49d00661fa"
#guard entryAddress.hex = "1437a122e15ed5fd0fe9e9933d1deec1e010def465b65a2b662aeb1549c3705b"
#guard Node.decode entryNode.encode = some entryNode
#guard Node.decode (entryNode.encode ++ [0]) = none
#guard Node.decode entryNode.encode.dropLast = none

/-- The kind-6 twin: the same payload filed as an annotation, another address. -/
def entryTwin : Node := ⟨0, .annotation, entrySpec, Canonical.toVal Templates.entry⟩

#guard (sha256 entryTwin.encode).hex = "ca07857e6301ef7b052d889bc1296cd280d13e7050b9326235333533b7ba0990"
#guard sha256 entryTwin.encode ≠ entryAddress
#guard entryTwin.encode.drop 2 = entryNode.encode.drop 2

/-- `p42` at kind 5 with the zero spec. -/
def p42Node : Node := ⟨0, .program, zeroDigest, Canonical.toVal ProgramCanonical.Corpus.p42⟩

#guard (Canonical.encode ProgramCanonical.Corpus.p42).length = 66
#guard (Canonical.digest ProgramCanonical.Corpus.p42).hex =
  "fa5f40f054198e91b2446522308e197b0a02c4edfe823f894763d3aa63ad62a3"
#guard p42Node.encode.length = 34 + 66
#guard (sha256 p42Node.encode).hex = "8032405e589e111c77c13b95b8a2ea408627f4e855ee3e8891fb3ac51676c13a"
#guard Node.decode p42Node.encode = some p42Node

/-- `Entry` files as `export`; the instance the generator will emit for lane C. -/
instance instContentEntry : Content Templates.Entry := ⟨.«export»⟩

/-- The typed reference to the entry node. -/
def entryTyped : Ref Templates.Entry := ⟨entryAddress⟩

#guard (Canonical.encode entryTyped).length = 42
#guard (Canonical.encode entryTyped).take 10 = [0x0b, 0, 0, 0, 0, 0, 0, 0, 0x21, 0x02]
#guard (Canonical.encode entryTyped).drop 10 = entryAddress.bytes
#guard Canonical.decode (α := Ref Templates.Entry) (Canonical.encode entryTyped) = some entryTyped
#guard Canonical.decode (α := Ref Templates.Entry) (Val.encode (.ref 6 entryAddress.bytes)) = none
#guard Canonical.decode (α := Ref Templates.Entry) (Val.encode (.ref 2 (entryAddress.bytes.drop 1))) = none
#guard Canonical.decode (α := AnyRef) (Canonical.encode entryTyped) = some ⟨.«export», entryAddress⟩
#guard (Canonical.shape (Ref Templates.Entry)).accepts (Canonical.toVal entryTyped) = true
#guard (Canonical.shape (Ref Templates.Entry)).accepts (.ref 6 entryAddress.bytes) = false

/-! ## The store under the seeded spec: `fresh`, `duplicate`, `dangling`, `wrongKind` -/

/-- A stand-in schema node seeded under today's `entryDoc` address. The key is not the node's
hash — the number comes from the old store — and `verify` says so. -/
def seededSpec : Node := ⟨0, .schema, zeroDigest, .str "entryDoc"⟩

/-- The seeded store: the stand-in under the spec key, nothing else. -/
def seeded : Store := ⟨[(entrySpec, seededSpec)], []⟩

#guard outcomeIs (seeded.putNode entryNode) .fresh
#guard (match seeded.putNode entryNode with
  | .ok (.fresh, d, s) => d = entryAddress && s.find entryAddress = some entryNode
  | _ => false)
#guard outcomeIs ((afterPut seeded entryNode).putNode entryNode) .duplicate
#guard (afterPut (afterPut seeded entryNode) entryNode).nodes.length = 2
#guard outcomeIs ((afterPut seeded entryNode).putNode entryTwin) .fresh
#guard (afterPut (afterPut seeded entryNode) entryTwin).nodes.length = 3
#guard (afterPut (afterPut seeded entryNode) entryTwin).find (sha256 entryTwin.encode) = some entryTwin
#guard outcomeIs (seeded.putNode ⟨0, .program, entrySpec, Canonical.toVal ProgramCanonical.Corpus.p42⟩) .fresh
#guard refusedWith (Store.empty.putNode entryNode) (.dangling entrySpec)
#guard refusedWith (Store.empty.putNode p42Node) (.dangling zeroDigest)
#guard refusedWith (seeded.putNode p42Node) (.dangling zeroDigest)
#guard refusedWith ((Store.mk [(entrySpec, ⟨0, .tree, zeroDigest, .list []⟩)] []).putNode entryNode)
  (.wrongKind entrySpec .schema .tree)
#guard refusedWith ((afterPut seeded entryNode).putNode ⟨0, .tree, entrySpec, .ref 6 entryAddress.bytes⟩)
  (.wrongKind entryAddress .annotation .«export»)
#guard outcomeIs ((afterPut seeded entryNode).putNode ⟨0, .tree, entrySpec, .ref 2 entryAddress.bytes⟩) .fresh
#guard (match seeded.verify with
  | .error (.digestMismatch d) => d = entrySpec
  | _ => false)
#guard (match (Store.mk [(entrySpec, ⟨0, .schema, zeroDigest, .str "entryDoc"⟩), (entryAddress, entryNode)] []).verify with
  | .error (.digestMismatch d) => d = entrySpec
  | _ => false)

/-! ## The word, the closure, the layered read, the outbox, verify, the trait: the genuine world -/

#guard probeEntry = ⟨0, .«export», probeSchemaAddress, Canonical.toVal Templates.entry⟩
#guard probeWord.wf = true
#guard Word.wf probeWord.reverse = false
#guard (replayed probeWord).nodes = probeStore.nodes
#guard (match Word.apply probeWord (replayed probeWord) with
  | .ok s => s.nodes = (replayed probeWord).nodes
  | .error _ => false)
#guard probeStore.closure ⟨.«export», probeEntryAddress⟩ = probeWord
#guard (Layered.mk Store.empty probeStore).getNode probeEntryAddress = some probeEntry
#guard (Layered.mk probeStore Store.empty).getNode probeEntryAddress = some probeEntry
#guard probeLocal.outbox = probeWord
#guard (match probeLocal.sync Store.empty with
  | .ok r => r.nodes = probeStore.nodes &&
    (match probeLocal.sync r with
      | .ok r' => r'.nodes = r.nodes
      | .error _ => false)
  | .error _ => false)
#guard verified probeStore.verify
#guard (match (Store.mk [(probeSchemaAddress, probeSchema),
    (probeEntryAddress, ⟨0, .«export», probeSchemaAddress,
      .ctor 0 [.str "Effect", .str "gen", .ctor 0 [], .nat 1946]⟩)] []).verify with
  | .error (.digestMismatch d) => d = probeEntryAddress
  | _ => false)
#guard traitStore.traitsOf entryRef = [(trait1Address, trait1Node)]
#guard traitStore.find probeEntryAddress = some probeEntry
#guard (traitStore.find probeEntryAddress).map Node.encode = some probeEntry.encode
#guard (afterPut traitStore trait2Node).find probeEntryAddress = some probeEntry

/-! ## The lattice and the typed face, stated (instantiable once `Content Document` exists) -/

#check @address_eq_or_collision
#check @address_inj
#check @metaSchema_accepts
#check @get_put
#check @put_duplicate
#check @put_preserves
#check @wf_closed
#check @apply_idempotent
#check @closure_closed
#check @layered_get
#check @outbox_wf
#check @sync_sub
#check @verify_sound
#check @traitsOf_perm

/-! ## Receipts -/

#print axioms entrySpec
#print axioms entryNode
#print axioms entryAddress
#print axioms entryTwin
#print axioms p42Node
#print axioms instContentEntry
#print axioms entryTyped
#print axioms seededSpec
#print axioms seeded

end Effect4.Store
