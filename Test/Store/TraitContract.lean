/-
Contract: traits as typed annotation nodes and their resolution (`src/Effect4/Store/Traits.lean`).

Frozen: the four rules of `docs/research/2026-09-04-cas-trait-facts.md` §5, Q8. A trait is an
`annotation` node (kind 6) whose payload is content — a subject, a value, and an optional
`prev` — so it is put, addressed and verified like anything else. Traits never enter identity:
the subject's bytes and address are the same before and after any number of traits are put on
it. `effective` resolves node, then spec, then the kind-registry row, most specific first, and
supersession through `prev` moves the head without deleting anything.

The fixtures are the substrate's own (`Store/Traits.lean`): a trait spec under the stand-in
genesis, a trait on the census entry, the trait that supersedes it, a trait on the entry's
spec node, a registry tree with a default trait, and two further exports that resolve at the
spec and registry levels.

Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Store.Traits

namespace Test.Store.TraitContract

open Effect4.Store

/-! ## A trait is content -/

-- The payload is a `ctor` frame of a subject reference, a value, and an optional previous
-- reference: 42 bytes of `anyRef`, the value's frame, and the option's.
#guard (Canonical.encode trait1).length = 9 + 9 + 42 + (9 + 7) + 9
#guard Content.kind (Annotation String) = .annotation
#guard (Content.kind (Annotation String)).byte = 6
#guard (Canonical.decode (α := Annotation String) (Canonical.encode trait1)).map Canonical.toVal
  = some (Canonical.toVal trait1)
#guard (Canonical.decode (α := Annotation String) (Canonical.encode trait2)).map Canonical.toVal
  = some (Canonical.toVal trait2)
#guard (Canonical.shape (Annotation String)).accepts (Canonical.toVal trait2) = true

-- The subject and `prev` are typed references, refused at a wrong kind byte or a short
-- address before any store is consulted; a wrong constructor index is refused too.
#guard Canonical.ofVal (α := Annotation String)
  (.ctor 0 [Canonical.toVal entryRef, .str "x", .some (.ref 2 trait1Address.bytes)]) = none
#guard Canonical.ofVal (α := Annotation String)
  (.ctor 0 [Canonical.toVal entryRef, .str "x", .some (.ref 6 (trait1Address.bytes.drop 1))])
  = none
#guard Canonical.ofVal (α := Annotation String)
  (.ctor 1 [Canonical.toVal entryRef, .str "x", .none]) = none

-- The edges a trait node carries are exactly its subject and, when it has one, its `prev`.
#guard trait1Node.refsOf = [entryRef]
#guard trait1Node.subjectOf = some entryRef
#guard trait1Node.prevOf = none
#guard trait2Node.prevOf = some trait1Address

/-! ## A trait is admitted like anything else -/

-- Its spec must be resident first; then it enters fresh.
#guard refusedWith (probeStore.putNode trait1Node) (.dangling traitSpecAddress)
#guard outcomeIs ((afterPut probeStore traitSpec).putNode trait1Node) .fresh
#guard traitStore.nodes.length = 9

/-! ## Traits never enter identity -/

-- Nine nodes on top of the entry, and the entry is byte for byte the node it was, at the
-- address it was: `nodeBytes` reads the shape and the identity-bound plane only.
#guard traitStore.find probeEntryAddress = some probeEntry
#guard (traitStore.find probeEntryAddress).map Node.encode = some probeEntry.encode
#guard (afterPut traitStore trait2Node).find probeEntryAddress = some probeEntry
#guard (afterPut traitStore trait2Node).find probeEntryAddress = traitStore.find probeEntryAddress
#guard sha256 probeEntry.encode = probeEntryAddress

/-! ## Resolution, most specific first -/

-- At the node: the entry's own trait.
#guard traitStore.traitsOf entryRef = [(trait1Address, trait1Node)]
#guard traitStore.effective registryAddress entryRef traitSpecAddress =
  [(trait1Address, trait1Node)]
-- An unknown key answers nothing rather than the wrong thing.
#guard traitStore.effective registryAddress entryRef probeSchemaAddress = []
-- At the spec: a second export under the same spec has no trait of its own and inherits the
-- trait on that spec node.
#guard traitStore.effective registryAddress ⟨.«export», sha256 export2.encode⟩ traitSpecAddress
  = [(sha256 trait3Node.encode, trait3Node)]
-- At the registry: a third export whose spec carries no trait falls through to the kind row.
#guard traitStore.effective registryAddress ⟨.«export», sha256 export3.encode⟩ traitSpecAddress
  = [(sha256 trait4Node.encode, trait4Node)]
-- With no registry there is nothing left to fall through to.
#guard traitStore.effective zeroDigest ⟨.«export», sha256 export3.encode⟩ traitSpecAddress = []

/-! ## Supersession -/

-- The superseding trait is an ordinary put; it moves the head without removing the trait it
-- supersedes, and the subject is still untouched.
#guard outcomeIs (traitStore.putNode trait2Node) .fresh
#guard (afterPut traitStore trait2Node).traitsOf entryRef = [(trait2Address, trait2Node)]
#guard (afterPut traitStore trait2Node).superseded trait1Address = true
#guard (afterPut traitStore trait2Node).superseded trait2Address = false
#guard (afterPut traitStore trait2Node).find trait1Address = some trait1Node
#guard (afterPut traitStore trait2Node).effective registryAddress entryRef traitSpecAddress
  = [(trait2Address, trait2Node)]
#guard verified (afterPut traitStore trait2Node).verify

/-! ## The laws, stated -/

#check @Effect4.Store.nodeBytes_trait_free
#check @Effect4.Store.trait_put_preserves
#check @Effect4.Store.trait_get_preserves
#check @Effect4.Store.effective_deterministic
#check @Effect4.Store.traitsOf_perm
#check @Effect4.Store.headsUnder_perm

/-! ## Axiom receipts -/

#print axioms Effect4.Store.Annotation.shapeDoc
#print axioms Effect4.Store.Store.annotationsOf
#print axioms Effect4.Store.Store.superseded
#print axioms Effect4.Store.Store.traitsOf
#print axioms Effect4.Store.Store.headsUnder
#print axioms Effect4.Store.Store.effective
#print axioms Effect4.Store.nodeBytes_trait_free
#print axioms Effect4.Store.trait_put_preserves
#print axioms Effect4.Store.trait_get_preserves
#print axioms Effect4.Store.effective_deterministic
#print axioms Effect4.Store.traitsOf_perm
#print axioms Effect4.Store.headsUnder_perm

end Test.Store.TraitContract
