/-
Contract: the node layer — kinds, typed references, node bytes, and the genesis
(`Effect4/Store/{Kind,Node,Genesis}.lean`).

Frozen: the kind byte of every kind and its round trip; the two refusals a typed `Ref` makes
before any store is consulted (a wrong kind byte, a wrong address length); the census entry's
node under the stand-in spec of `docs/research/2026-09-04-cas-trait-facts.md` §6 — 108 bytes at
`1437a1…705b`, with the kind-6 twin `ca0785…0990` that shows one payload at two kinds is two
addresses; and the §6a numbers the spike's exit fixed once `Canonical Document` existed: the
meta-schema's 92,462-byte payload, the genesis address `2794d9…2926`, the entry's real spec
`268ee1…aa7c` and its real address `1c3c94…72eb`.

`Templates.Entry` files as `export` content here rather than in the library: nothing in `src/`
carries this four-field shape (the census entry gained a `source : Ref Source` field at the
landing, `StdLib/Entry.lean`), so the illustration's kind belongs with the
illustration. `Store/Val.lean`'s `sampleEntry` is its value tree, which is why the §6 and §6a
numbers still hold.

Measured 2026-09-05 (lane B, `docs/research/2026-09-05-workshop-cas/NOTES-B.md`): the whole file, genesis guards
included, elaborates in seconds — `#guard` evaluates the compiled `Decidable` instance rather
than reducing it in the kernel, so a SHA-256 over ninety-two kilobytes costs a fraction of a
second and the §6a addresses are guarded, not printed.

Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Store.Genesis
import Test.Store.Templates

namespace Test.Store.NodeContract

open Effect4.Store

/-! ## The kinds -/

-- The table of `docs/research/2026-09-04-cas-trait-plan.md` §3. Bytes are identity: appended,
-- never renumbered, and the reserved rows are present so a later consumer cannot take a byte
-- that is already spoken for.
#guard Kind.all.length = 15
#guard Kind.all.map Kind.byte = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
#guard Kind.all.map Kind.name =
  ["source", "export", "type", "schema", "program", "annotation", "entry", "query", "result",
   "chunk", "tree", "manifest", "component", "vector", "fiber"]

-- The round trip both ways, and the two ends of the alphabet refused.
#guard Kind.all.all fun k => Kind.ofByte? k.byte = some k
#guard Kind.all.all fun k => Kind.ofName? k.name = some k
#guard Kind.ofByte? 0 = none
#guard Kind.ofByte? 16 = none
#guard Kind.ofName? "enum" = none

#check @Effect4.Store.Kind.ofByte?_byte
#check @Effect4.Store.Kind.byte_ofByte?
#check @Effect4.Store.Kind.byte_injective
#check @Effect4.Store.Kind.name_injective

/-! ## The census entry as content -/

/-- `Templates.Entry` files as `export`, the kind the plan's §3 gives the census entry. -/
instance instContentEntry : Content Effect4.Store.Templates.Entry := ⟨.«export»⟩

#guard Content.kind Effect4.Store.Templates.Entry = .«export»
#guard (Content.kind Effect4.Store.Templates.Entry).byte = 2

/-! ## The node under the stand-in spec (facts note §6) -/

/-- The address today's JSON-route `entryDoc` had before the landing. The facts note used it as
a stand-in for the spec while `Canonical Document` did not exist; it is kept because the node
layer is exactly the arithmetic that does not depend on which document the spec names. -/
def entrySpecHex : String := "6a1c902ee204a7856387132a13975908fd4d891c7cc1a55e3179ddaf5e01cac8"

/-- The stand-in spec as a digest. -/
def entrySpec : Digest := (Digest.ofHex? entrySpecHex).getD zeroDigest

#guard (Digest.ofHex? entrySpecHex).isSome
#guard entrySpec.hex = entrySpecHex

/-- The entry node of the facts note: `00 │ 02 │ spec (32) │ payload (74)`, 108 bytes. -/
def entryNode : Node := ⟨0, .«export», entrySpec, Canonical.toVal Effect4.Store.Templates.entry⟩

/-- Its address, the facts note's `Ref Entry` under the stand-in spec. -/
def entryAddress : Digest := sha256 entryNode.encode

#guard Canonical.toVal Effect4.Store.Templates.entry = sampleEntry
#guard entryNode.encode.length = 108
-- The header is the version byte and the kind byte, then the spec, then the payload.
#guard entryNode.encode.take 2 = [0x00, 0x02]
#guard (entryNode.encode.drop 2).take 32 = entrySpec.bytes
#guard entryNode.encode.drop 34 = Val.encode sampleEntry
#guard (sha256 (Val.encode sampleEntry)).hex =
  "8fab161870afe7d35c681679cf5dced52845b5ebef2b84b6c85e4b49d00661fa"
#guard entryAddress.hex = "1437a122e15ed5fd0fe9e9933d1deec1e010def465b65a2b662aeb1549c3705b"

-- The node codec is exact: nothing appended, nothing dropped.
#guard Node.decode entryNode.encode = some entryNode
#guard Node.decode (entryNode.encode ++ [0]) = none
#guard Node.decode entryNode.encode.dropLast = none

/-- The kind-6 twin: the same payload under the same spec, filed as an annotation. -/
def entryTwin : Node := ⟨0, .annotation, entrySpec, Canonical.toVal Effect4.Store.Templates.entry⟩

-- One payload at two kinds is two addresses; everything after the kind byte agrees.
#guard (sha256 entryTwin.encode).hex =
  "ca07857e6301ef7b052d889bc1296cd280d13e7050b9326235333533b7ba0990"
#guard sha256 entryTwin.encode ≠ entryAddress
#guard entryTwin.encode.drop 2 = entryNode.encode.drop 2

/-! ## The typed reference -/

/-- The typed reference to the entry node. -/
def entryTyped : Ref Effect4.Store.Templates.Entry := ⟨entryAddress⟩

-- Forty-two bytes: the `ref` tag, the length, the kind byte, the thirty-two address bytes.
#guard (Canonical.encode entryTyped).length = 42
#guard (Canonical.encode entryTyped).take 10 = [0x0b, 0, 0, 0, 0, 0, 0, 0, 0x21, 0x02]
#guard (Canonical.encode entryTyped).drop 10 = entryAddress.bytes
#guard Canonical.decode (α := Ref Effect4.Store.Templates.Entry) (Canonical.encode entryTyped) =
  some entryTyped
-- A wrong kind byte, and a wrong address length: both refused at decode, before any store is
-- consulted.
#guard Canonical.decode (α := Ref Effect4.Store.Templates.Entry)
  (Val.encode (.ref 6 entryAddress.bytes)) = none
#guard Canonical.decode (α := Ref Effect4.Store.Templates.Entry)
  (Val.encode (.ref 2 (entryAddress.bytes.drop 1))) = none
-- An untyped reference reads the kind off the frame instead of the type.
#guard Canonical.decode (α := AnyRef) (Canonical.encode entryTyped) =
  some ⟨.«export», entryAddress⟩
#guard (Canonical.shape (Ref Effect4.Store.Templates.Entry)).accepts (Canonical.toVal entryTyped)
  = true
#guard (Canonical.shape (Ref Effect4.Store.Templates.Entry)).accepts (.ref 6 entryAddress.bytes)
  = false

/-! ## The genesis and the real spec (facts note §6a) -/

-- The meta-schema is the document of `Document`'s own shape, and it is the unique zero-spec
-- node: `specFor` chooses zero exactly there.
#guard (Val.encode (Canonical.toVal metaSchema)).length = 92462
#guard decide (specFor metaSchema = zeroDigest)
#guard genesisNode.kind = .schema
#guard genesisNode.spec = zeroDigest
#guard genesisNode.IsGenesis

-- The genesis address is the spec of every other schema node, and it is `specOf Document`.
#guard genesisAddress.hex =
  "2794d94c40e85c5643ebc081a54eed287da0e746537f4f8ecfd4efc3020c2926"
#guard (specOf Effect4.Document).hex = genesisAddress.hex
#guard specOf Effect4.Document = genesisAddress

-- The entry's real spec: its shape's document, filed as a schema node under the genesis.
#guard (Val.encode (Canonical.toVal (Canonical.document Effect4.Store.Templates.Entry))).length
  = 1270
#guard (specOf Effect4.Store.Templates.Entry).hex =
  "268ee1186c537706faf2301564250676c3ed971565e7c67a36c9d19e0dc8aa7c"

-- The entry's real address, which supersedes the stand-in `1437a1…705b` above: the same 108
-- bytes with the real spec in the header.
#guard (nodeOf Effect4.Store.Templates.entry).encode.length = 108
#guard (nodeOf Effect4.Store.Templates.entry).spec = specOf Effect4.Store.Templates.Entry
#guard (address Effect4.Store.Templates.entry).digest.hex =
  "1c3c94979c106a7b40c332fe03f7ad26345e2f5588b313ce6e731f32067272eb"
#guard (address Effect4.Store.Templates.entry).digest ≠ entryAddress

-- A schema node whose spec is not the meta-schema's address is not a schema node of this
-- store: only the genesis is exempt, and `specFor` gives it zero and everything else the
-- genesis address.
#guard (nodeOf metaSchema).spec = zeroDigest
#guard (nodeOf (Canonical.document Effect4.Store.Templates.Entry)).spec = genesisAddress
#guard ¬ (nodeOf (Canonical.document Effect4.Store.Templates.Entry)).IsGenesis

/-! ## The address lattice, stated -/

#check @Effect4.Store.address_congr
#check @Effect4.Store.address_eq_or_collision
#check @Effect4.Store.address_inj
#check @Effect4.Store.Node.decode_encode
#check @Effect4.Store.Node.decode_exact
#check @Effect4.Store.Node.encode_injective
#check @Effect4.Store.metaSchema_accepts
#check @Effect4.Store.specOf_document

/-! ## Axiom receipts -/

#print axioms Effect4.Store.Kind.byte
#print axioms Effect4.Store.Kind.ofByte?_byte
#print axioms Effect4.Store.Kind.byte_injective
#print axioms Effect4.Store.Kind.name_injective
#print axioms Effect4.Store.Node.encode
#print axioms Effect4.Store.Node.decode
#print axioms Effect4.Store.Node.decode_encode
#print axioms Effect4.Store.Node.decode_exact
#print axioms Effect4.Store.Node.encode_injective
#print axioms Effect4.Store.instCanonicalRef
#print axioms Effect4.Store.instCanonicalAnyRef
#print axioms Effect4.Store.metaSchema
#print axioms Effect4.Store.genesisNode
#print axioms Effect4.Store.genesisAddress
#print axioms Effect4.Store.specOf
#print axioms Effect4.Store.specFor
#print axioms Effect4.Store.nodeOf
#print axioms Effect4.Store.address
#print axioms Effect4.Store.address_eq_or_collision
#print axioms Effect4.Store.address_inj
#print axioms Effect4.Store.specOf_document
#print axioms Effect4.Store.metaSchema_accepts
#print axioms instContentEntry
#print axioms entrySpec
#print axioms entryNode
#print axioms entryAddress
#print axioms entryTwin
#print axioms entryTyped

end Test.Store.NodeContract
