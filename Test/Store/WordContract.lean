/-
Contract: admission, words, closures, the layered read, the outbox and verification
(`Effect4/Store/{Store,Word}.lean`).

Frozen: the three put outcomes (`fresh`, `duplicate`, `conflict`) and the refusals that come
before them (`dangling`, `wrongKind`, `badVersion`, `malformedRef`), each on a real address —
the hash of a real node, never a literal; that a `wf` word replays to the store it was cut
from and replaying it again changes nothing; that a root's closure is a children-first word;
that a layered read answers from the local store first and falls through to the remote; that
an outbox synced twice is the same remote; that `verify` passes on a sound store and refuses
after one byte of one payload is flipped; and that a root move under a stale version is
refused rather than merged.

The fixtures are the substrate's own (`Store/Store.lean`, `Store/Word.lean`): a stand-in
genesis `probeSchema` (kind `schema`, zero spec), the census entry `probeEntry` under it, and
the two-binding word `probeWord`. They are library declarations because the substrate proves
its laws against them; this battery is what says the *behaviour* is frozen, and it adds what
the library does not guard — the layered read in both directions, `Word.apply` run twice
through the store the word already built, and the stale-root refusal read out of its error.

Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Store.Word

namespace Test.Store.WordContract

open Effect4.Store

/-! ## The three outcomes -/

-- A genesis-shaped node enters an empty store; the entry under it enters fresh; either put
-- again is a duplicate and the store does not grow.
#guard outcomeIs (Store.empty.putNode probeSchema) .fresh
#guard outcomeIs ((afterPut Store.empty probeSchema).putNode probeEntry) .fresh
#guard outcomeIs (probeStore.putNode probeEntry) .duplicate
#guard outcomeIs (probeStore.putNode probeSchema) .duplicate
#guard probeStore.nodes.length = 2
#guard (afterPut probeStore probeEntry).nodes.length = 2

-- The address a put answers is the hash of the node's bytes, and the node is found there.
#guard (match Store.empty.putNode probeSchema with
  | .ok (_, d, s) => d = sha256 probeSchema.encode && s.find d = some probeSchema
  | .error _ => false)
#guard probeStore.find probeEntryAddress = some probeEntry
#guard probeStore.getNode probeSchemaAddress = some probeSchema
#guard probeStore.find zeroDigest = none

-- A conflict is an exhibited collision: the store keeps bytes, so an occupant at the address
-- is surfaced and never overwritten.
#guard outcomeIs ((Store.mk [(probeSchemaAddress, probeSchema),
    (probeEntryAddress, ⟨0, .«export», probeSchemaAddress, .nat 1⟩)] []).putNode probeEntry)
  (.conflict ⟨0, .«export», probeSchemaAddress, .nat 1⟩)
#guard (afterPut (Store.mk [(probeSchemaAddress, probeSchema),
    (probeEntryAddress, ⟨0, .«export», probeSchemaAddress, .nat 1⟩)] []) probeEntry).nodes.length
  = 2

/-! ## The refusals, on real addresses -/

-- The spec edge of a non-genesis node must resolve: the entry alone dangles at its spec.
#guard refusedWith (Store.empty.putNode probeEntry) (.dangling probeSchemaAddress)
-- Only the genesis carries the zero spec.
#guard refusedWith (probeStore.putNode ⟨0, .«export», zeroDigest, sampleEntry⟩)
  (.dangling zeroDigest)
-- A typed reference must resolve at its own kind.
#guard refusedWith
  (probeStore.putNode ⟨0, .tree, probeSchemaAddress, .ref 2 probeSchemaAddress.bytes⟩)
  (.wrongKind probeSchemaAddress .«export» .schema)
#guard outcomeIs
  (probeStore.putNode ⟨0, .tree, probeSchemaAddress, .ref 2 probeEntryAddress.bytes⟩) .fresh
-- Version byte 0 is the only version, and a reference frame at an unregistered kind byte or a
-- short address is malformed before any lookup.
#guard refusedWith (probeStore.putNode ⟨1, .«export», probeSchemaAddress, sampleEntry⟩)
  .badVersion
#guard refusedWith
  (probeStore.putNode ⟨0, .tree, probeSchemaAddress, .ref 16 probeEntryAddress.bytes⟩)
  .malformedRef
#guard refusedWith
  (probeStore.putNode ⟨0, .tree, probeSchemaAddress, .ref 2 (probeEntryAddress.bytes.drop 1)⟩)
  .malformedRef

/-! ## Words -/

-- The word is children-first: the spec before the node that cites it, and the reverse is not
-- well formed. A binding whose key is not the hash of its node is not well formed either.
#guard probeWord = [⟨probeSchemaAddress, probeSchema⟩, ⟨probeEntryAddress, probeEntry⟩]
#guard probeWord.wf = true
#guard Word.wf probeWord.reverse = false
#guard Word.wf [⟨probeEntryAddress, probeEntry⟩] = false
#guard Word.wf [⟨probeSchemaAddress, probeEntry⟩] = false

-- A well-formed word replays into the store it was cut from, and replaying it there again
-- changes nothing: `apply` is idempotent.
#guard (replayed probeWord).nodes = probeStore.nodes
#guard (match Word.apply probeWord (replayed probeWord) with
  | .ok s => s.nodes = (replayed probeWord).nodes ∧ s.roots = (replayed probeWord).roots
  | .error _ => false)
-- The reverse word refuses where the spec is missing, at the address it is missing at.
#guard (match Word.apply probeWord.reverse Store.empty with
  | .error (.dangling d) => d = probeSchemaAddress
  | _ => false)

-- The closure of a root is that word: the reachable subgraph, children first.
#guard probeStore.closure ⟨.«export», probeEntryAddress⟩ = probeWord
#guard probeStore.closure ⟨.schema, probeSchemaAddress⟩ = [⟨probeSchemaAddress, probeSchema⟩]
#guard probeStore.closure ⟨.schema, zeroDigest⟩ = []
#guard (probeStore.closure ⟨.«export», probeEntryAddress⟩).wf = true

/-! ## The layered read and the outbox -/

-- A layered store reads the local plane first and falls through to the remote; the same node
-- is found whichever plane holds it, and an address neither holds is nothing.
#guard (Layered.mk Store.empty probeStore).getNode probeEntryAddress = some probeEntry
#guard (Layered.mk probeStore Store.empty).getNode probeEntryAddress = some probeEntry
#guard (Layered.mk Store.empty probeStore).getNode zeroDigest = none
-- Preload is the closure applied to the local plane.
#guard (match (Layered.mk Store.empty probeStore).preload ⟨.«export», probeEntryAddress⟩ with
  | .ok l => l.local.find probeEntryAddress = some probeEntry ∧ l.local.nodes.length = 2
  | .error _ => false)

-- Local-first: every put lands locally and is appended to the outbox, so the outbox is the
-- word of what the remote has not seen.
#guard probeLocal.outbox = probeWord
#guard probeLocal.local.nodes = probeStore.nodes
#guard (match probeLocal.putNode probeEntry with
  | .ok (.duplicate, _, l) => l.outbox = probeWord && l.local.nodes = probeStore.nodes
  | _ => false)

-- Sync is replay, and syncing twice is syncing once: the second run is all duplicates.
#guard (match probeLocal.sync Store.empty with
  | .ok r => r.nodes = probeStore.nodes &&
    (match probeLocal.sync r with
      | .ok r' => r'.nodes = r.nodes
      | .error _ => false)
  | .error _ => false)
#guard (match probeLocal.sync probeStore with
  | .ok r => r.nodes = probeStore.nodes
  | .error _ => false)

/-! ## Verification -/

-- A store built by `putNode` verifies, and so does the store a word replays into.
#guard verified probeStore.verify
#guard verified (replayed probeWord).verify

-- One byte of one payload flipped — the entry's line 1947 = `0x079b` becomes 1946 = `0x079a`
-- — and the node no longer hashes to the key it is filed under. `verify` names that key.
#guard (match (Store.mk [(probeSchemaAddress, probeSchema),
    (probeEntryAddress, ⟨0, .«export», probeSchemaAddress,
      .ctor 0 [.str "Effect", .str "gen", .ctor 0 [], .nat 1946]⟩)] []).verify with
  | .error (.digestMismatch d) => d = probeEntryAddress
  | _ => false)
-- A node whose spec is not resident: `verify` names the node and what it wanted.
#guard (match (Store.mk [(probeEntryAddress, probeEntry)] []).verify with
  | .error (.dangling node missing) => node = probeEntryAddress ∧ missing = probeSchemaAddress
  | _ => false)

/-! ## Roots, the one mutable plane -/

-- A root moves under compare-and-set, and the name answers the new root.
#guard (match probeStore.putRoot ⟨"stdlib/rc112", .stdlib, .«export», probeEntryAddress, 1⟩ with
  | .ok s => s.root? "stdlib/rc112" =
      some ⟨"stdlib/rc112", .stdlib, .«export», probeEntryAddress, 1⟩
  | .error _ => false)
-- A stale version is refused, never merged: the error carries the version held and the
-- version offered.
#guard (match probeStore.putRoot ⟨"stdlib/rc112", .stdlib, .«export», probeEntryAddress, 2⟩ with
  | .error (.staleRoot "stdlib/rc112" 1 2) => true
  | _ => false)
-- A root must name a resident node of its own kind.
#guard (match probeStore.putRoot ⟨"stdlib/rc112", .stdlib, .schema, probeEntryAddress, 1⟩ with
  | .error (.wrongKind _ .schema .«export») => true
  | _ => false)
#guard (match probeStore.putRoot ⟨"stdlib/rc112", .stdlib, .«export», zeroDigest, 1⟩ with
  | .error (.dangling _) => true
  | _ => false)
-- A root the store does not resolve at its kind fails verification.
#guard (match (Store.mk probeStore.nodes
    [⟨"stdlib/rc112", .stdlib, .schema, probeEntryAddress, 1⟩]).verify with
  | .error (.rootUnresolved name) => name = "stdlib/rc112"
  | _ => false)
#guard verified (Store.mk probeStore.nodes
  [⟨"stdlib/rc112", .stdlib, .«export», probeEntryAddress, 1⟩]).verify

/-! ## The laws, stated -/

#check @Effect4.Store.get_put
#check @Effect4.Store.put_duplicate
#check @Effect4.Store.put_conflict
#check @Effect4.Store.put_preserves
#check @Effect4.Store.putNode_closed
#check @Effect4.Store.putRoot_root?
#check @Effect4.Store.empty_closed
#check @Effect4.Store.wf_closed
#check @Effect4.Store.apply_idempotent
#check @Effect4.Store.closure_wf
#check @Effect4.Store.closure_closed
#check @Effect4.Store.layered_get
#check @Effect4.Store.outbox_wf
#check @Effect4.Store.sync_sub
#check @Effect4.Store.sync_idempotent
#check @Effect4.Store.verify_sound
#check @Effect4.Store.verify_roots

/-! ## Axiom receipts -/

#print axioms Effect4.Store.Store.putNode
#print axioms Effect4.Store.Store.getNode
#print axioms Effect4.Store.Store.find
#print axioms Effect4.Store.Store.putRoot
#print axioms Effect4.Store.Store.verify
#print axioms Effect4.Store.get_put
#print axioms Effect4.Store.put_duplicate
#print axioms Effect4.Store.put_preserves
#print axioms Effect4.Store.putNode_closed
#print axioms Effect4.Store.putRoot_root?
#print axioms Effect4.Store.Word.wf
#print axioms Effect4.Store.Word.apply
#print axioms Effect4.Store.apply_idempotent
#print axioms Effect4.Store.wf_closed
#print axioms Effect4.Store.Store.closure
#print axioms Effect4.Store.closure_wf
#print axioms Effect4.Store.closure_closed
#print axioms Effect4.Store.layered_get
#print axioms Effect4.Store.sync_sub
#print axioms Effect4.Store.sync_idempotent
#print axioms Effect4.Store.verify_sound
#print axioms Effect4.Store.verify_roots

end Test.Store.WordContract
