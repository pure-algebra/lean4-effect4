/-
Contract: the generic content-addressed store (`Effect4/Store/*`).

Frozen: the canonical framing, the SHA-256 address against two CAVP digests the
hash library itself pins, the trie's two lookup laws, and the store's put,
name and resolve behaviour. Doc comments cannot precede `#guard`, so the
receipts carry line comments.
-/

import Effect4.Store.Store
import Effect4.Store.Digest
import Effect4.Store.Trie
import Effect4.Store.Canonical

namespace Effect4Test.Store.StoreContract

open Effect4.Store

/-! ## The address -/

-- CAVP `Len = 0`: SHA-256 of the empty string.
#guard (sha256 []).hex = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

-- CAVP `Len = 24`.
#guard (sha256 [0xb4, 0x19, 0x0e]).hex =
  "dff2e73091f6c05e528896c4c831b9448653dc2ff043528f6769437bc7b975c2"

#guard (sha256 []).bytes.length = 32

-- The address is of the canonical bytes, so it is a function of the value.
#guard digestOf "Effect.gen" = digestOf "Effect.gen"
#guard digestOf "Effect.gen" ≠ digestOf "Effect.fork"
#guard digestOf (3 : Nat) ≠ digestOf "3"
#guard digestOf (some (3 : Nat)) ≠ digestOf [(3 : Nat)]
#guard digestOf ((1 : Nat), "a") ≠ digestOf ("a", (1 : Nat))

/-! ## The framing -/

#guard encode () = [9, 0, 0, 0, 0, 0, 0, 0, 0]
#guard encode true = [1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
#guard encode (0 : Nat) = [2, 0, 0, 0, 0, 0, 0, 0, 0]
#guard encode (256 : Nat) = [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0]
#guard encode "A" = [3, 0, 0, 0, 0, 0, 0, 0, 1, 65]
#guard encode "é" = [3, 0, 0, 0, 0, 0, 0, 0, 2, 0xc3, 0xa9]
#guard encode ([] : List Nat) = [4, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (encode ["a", "b"]).length = 9 + 2 * (9 + 1)
#guard (framed 7 [1, 2, 3]).length = 12

#check @Effect4.Store.framed_length
#check @Effect4.Store.framed_inj
#check @Effect4.Store.ne_of_encode_ne
#check @Effect4.Store.eq_of_encode_eq

-- The lawful carriers so far: strings (through `String.toByteArray_inj`), raw
-- bytes, booleans and unit. Naturals, lists, pairs and options carry the
-- encoding without the law yet; nothing states it for them.
example : Effect4.Store.LawfulCanonical String := inferInstance
example : Effect4.Store.LawfulCanonical Effect4.Store.Bytes := inferInstance
example : Effect4.Store.LawfulCanonical Bool := inferInstance
example : Effect4.Store.LawfulCanonical Unit := inferInstance

/-! ## The trie -/

-- Two names under one module.
def std : Trie Nat :=
  Trie.ofList [(["Effect", "gen"], 1), (["Effect", "fork"], 2), (["Schema", "Struct"], 3)]

#guard std.lookup ["Effect", "gen"] = some 1
#guard std.lookup ["Effect", "fork"] = some 2
#guard std.lookup ["Schema", "Struct"] = some 3
#guard std.lookup ["Effect"] = none
#guard std.lookup ["Effect", "gen", "x"] = none
#guard std.lookup [] = none
#guard std.size = 3

-- Prefix order: the module's own binding first, then its children in insertion order.
#guard std.entries =
  [(["Effect", "gen"], 1), (["Effect", "fork"], 2), (["Schema", "Struct"], 3)]
#guard std.under ["Effect"] = [(["Effect", "gen"], 1), (["Effect", "fork"], 2)]
#guard std.under ["Schema"] = [(["Schema", "Struct"], 3)]
#guard std.under ["Layer"] = []

-- A later write at a bound path replaces; at a prefix it binds the node itself.
#guard (std.insert ["Effect", "gen"] 9).lookup ["Effect", "gen"] = some 9
#guard (std.insert ["Effect", "gen"] 9).size = 3
#guard (std.insert ["Effect"] 7).lookup ["Effect"] = some 7
#guard (std.insert ["Effect"] 7).under ["Effect"] =
  [(["Effect"], 7), (["Effect", "gen"], 1), (["Effect", "fork"], 2)]

#check @Effect4.Store.Trie.lookup_insert_same
#check @Effect4.Store.Trie.lookup_insert_other

/-! ## The store -/

-- Put twice, held once: the id is stable and the store does not grow.
#guard
  let (i, s) := (Store.empty : Store String).put "Effect.gen"
  let (j, s') := s.put "Effect.gen"
  i = j ∧ s'.size = 1 ∧ s'.get i = some "Effect.gen"

-- Distinct contents receive successive ids.
#guard
  let (i, s) := (Store.empty : Store String).put "a"
  let (j, s') := s.put "b"
  i = 0 ∧ j = 1 ∧ s'.size = 2 ∧ s'.values = ["a", "b"]

-- A name resolves to the id and the value; an unbound name resolves to nothing.
#guard
  let (i, s) := (Store.empty : Store String).putAt ["Effect", "gen"] "const gen = …"
  s.resolve ["Effect", "gen"] = some (i, "const gen = …") ∧ s.resolve ["Effect", "fork"] = none

-- Two names for one content share the id.
#guard
  let (i, s) := (Store.empty : Store String).putAt ["Effect", "gen"] "body"
  let (j, s') := s.putAt ["Effect", "genAlias"] "body"
  i = j ∧ s'.size = 1 ∧ (s'.under ["Effect"]).map Prod.snd = [i, j]

-- The address of a held content is the address of its value.
#guard
  let (i, s) := (Store.empty : Store String).put "x"
  s.digestAt i = some (digestOf "x") ∧ s.find (digestOf "x") = some i ∧ s.find (digestOf "y") = none

#check @Effect4.Store.Store.get_put_new
#check @Effect4.Store.Store.put_new
#check @Effect4.Store.Store.put_held
#check @Effect4.Store.Store.size_put
#check @Effect4.Store.Store.resolve_name
#check @Effect4.Store.Store.resolve_name_other
#check @Effect4.Store.Store.get_name

/-! ## Axiom receipts -/

#print axioms Effect4.Store.framed_length
#print axioms Effect4.Store.framed_inj
#print axioms Effect4.Store.instLawfulCanonicalString
#print axioms Effect4.Store.Digest.sha256_length
#print axioms Effect4.Store.Trie.lookup_insert_same
#print axioms Effect4.Store.Trie.lookup_insert_other
#print axioms Effect4.Store.Store.get_put_new
#print axioms Effect4.Store.Store.put_new
#print axioms Effect4.Store.Store.put_held
#print axioms Effect4.Store.Store.size_put
#print axioms Effect4.Store.Store.get_name
#print axioms Effect4.Store.Store.resolve_name
#print axioms Effect4.Store.Store.resolve_name_other
#print axioms Effect4.Store.digestOf

end Effect4Test.Store.StoreContract
