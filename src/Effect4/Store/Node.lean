import Effect4.Store.Canonical

/-!
# Store.Node

Owner: the typed address, the node a store keeps, its one byte layout with the exact codec,
the edge scan, and the address lattice proved once over `Content`.

A `Ref α` is thirty-two bytes and a phantom: the digest of a node whose payload is an `α`
(the facts note, Q3). `AnyRef` carries its kind byte alongside, for the places a pointer's
target type is not fixed (an annotation's subject, a tree's entries). `Content α` is
`Canonical α` plus the kind the carrier files under; the kind byte is not injective on types,
so `Ref Receipt` and `Ref Claim` stay different Lean types over the same byte. Both reference
types frame as `Val.ref kind digest` (`Tag.ref = 11`, 42 bytes), and reading one refuses a
wrong kind byte or a wrong length before any store is consulted (Q4).

A node is `version ∷ kind ∷ spec ∷ payload` (Q3): the version byte is `0`, the kind byte is the
table of `Store.Kind`, the spec is the address of the schema node describing the payload's shape,
and the payload is the value tree's bytes. `Node.decode` is exact the way `Val.decode` is: the
version must be `0`, the kind byte must be registered, the spec is thirty-two bytes, the rest is
one value tree and nothing else (`decode_encode`, `decode_exact`). Edges are not stored: they are
read off the payload by scanning for `ref` frames in traversal order (`refsOf`), a departure
from Foldlab's refs array that keeps its design; edge 0, the spec, sits at a fixed header
offset (`edges`). A `ref` frame whose kind byte is unregistered or whose digest is not
thirty-two bytes is `malformedRef`, refused at admission.

The genesis (Q6): the meta-schema, `(shape Document).document`, is the unique node with the
zero spec; every other schema node's spec is the genesis's address, and every other node's spec
is the address of its shape's schema node. Since that spec is chosen per value (the meta-schema
itself gets zero, every other document gets the genesis's address), `nodeOf` reads it through
`specFor`, which is `specOf α` except at the genesis. The address lattice is stated once over
`Content`: level 0 needs no premise about the hash (equal addresses are equal carriers or an
exhibited collision), level 1 holds under a named `Function.Injective sha256` that is never an
instance, and level 2 is shown empty. Both levels take the well-formedness of the two payloads,
because `Val.encode` is injective only there (`Val.encode_injective`); admission refuses anything
else as `oversize`, so every stored node satisfies the premise.

Everything that needs `Canonical Document` — the meta-schema, the genesis, `specOf`, `nodeOf`,
`address` and their laws — is written under `variable [Content Document]`, so the module
compiles before lane G derives the instance and instantiates when it lands.
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Document)

/-! ## References -/

/-- A typed address: the digest of a node whose payload is an `α`. The type is a phantom, so the
bytes of a `Ref Receipt` and a `Ref Claim` are the same shape while the Lean types differ. -/
structure Ref (α : Type) where
  digest : Digest

theorem Ref.ext {α : Type} {a b : Ref α} (h : a.digest = b.digest) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Decidable equality by hand: `deriving` would demand `DecidableEq α` for the phantom. -/
instance Ref.instDecidableEq {α : Type} : DecidableEq (Ref α) := fun a b =>
  if h : a.digest = b.digest then isTrue (Ref.ext h)
  else isFalse fun e => h (congrArg Ref.digest e)

instance Ref.instRepr {α : Type} : Repr (Ref α) := ⟨fun r _ => repr r.digest⟩

/-- An address with its kind: a pointer whose target type is not fixed (an annotation's subject,
a tree's entries). -/
structure AnyRef where
  kind : Kind
  digest : Digest
deriving DecidableEq, Repr

/-- The canonical trait plus the kind the carrier files under. -/
class Content (α : Type) extends Canonical α where
  /-- The kind byte's row for every node carrying an `α`. -/
  kind : Kind

/-- A digest from exactly thirty-two bytes; the one length check the codecs share. -/
def Digest.ofBytes? (bs : Bytes) : Option Digest :=
  if h : bs.length = 32 then some ⟨bs, h⟩ else none

theorem Digest.ofBytes?_bytes (d : Digest) : Digest.ofBytes? d.bytes = some d := by
  cases d with
  | mk bs hl =>
    show (if h : bs.length = 32 then some (Digest.mk bs h) else none) = some (Digest.mk bs hl)
    rw [dif_pos hl]

theorem Digest.ofBytes?_exact {bs : Bytes} {d : Digest} (h : Digest.ofBytes? bs = some d) :
    d.bytes = bs := by
  unfold Digest.ofBytes? at h
  split at h
  · injection h with h
    subst h
    rfl
  · exact nomatch h

/-- A typed reference frames as `ref` with its carrier's kind byte; reading refuses another kind
byte or a digest that is not thirty-two bytes. -/
instance instCanonicalRef {α : Type} [Content α] : Canonical (Ref α) where
  shape := ⟨.ref (Content.kind α), []⟩
  toVal r := .ref (Content.kind α).byte r.digest.bytes
  ofVal
    | .ref b d => if b = (Content.kind α).byte then (Digest.ofBytes? d).map Ref.mk else none
    | _ => none
  ofVal_toVal r := by
    show (if (Content.kind α).byte = (Content.kind α).byte then
      (Digest.ofBytes? r.digest.bytes).map Ref.mk else none) = some r
    rw [if_pos rfl, Digest.ofBytes?_bytes, Option.map_some]
  ofVal_exact := by
    intro v r h
    cases v
    case ref b d =>
      change (if b = (Content.kind α).byte then (Digest.ofBytes? d).map Ref.mk else none) = some r at h
      split at h
      · next hb =>
        obtain ⟨dg, hdg, hr⟩ := Option.map_eq_some_iff.mp h
        subst hr
        show Val.ref b d = Val.ref (Content.kind α).byte dg.bytes
        rw [hb, Digest.ofBytes?_exact hdg]
      · exact nomatch h
    all_goals exact nomatch h
  fits r := by
    show acceptsIn [] (.ref (Content.kind α)) (.ref (Content.kind α).byte r.digest.bytes) = true
    simp [acceptsIn, candidates, acceptsAt, r.digest.length_eq]

/-- An untyped reference frames as `ref` with its own kind byte; reading refuses an unregistered
byte or a digest that is not thirty-two bytes. -/
instance instCanonicalAnyRef : Canonical AnyRef where
  shape := ⟨.anyRef, []⟩
  toVal r := .ref r.kind.byte r.digest.bytes
  ofVal
    | .ref b d =>
      match Kind.ofByte? b, Digest.ofBytes? d with
      | some k, some dg => some ⟨k, dg⟩
      | _, _ => none
    | _ => none
  ofVal_toVal r := by
    obtain ⟨k, d⟩ := r
    show (match Kind.ofByte? k.byte, Digest.ofBytes? d.bytes with
      | some k, some dg => some (AnyRef.mk k dg)
      | _, _ => none) = some (AnyRef.mk k d)
    rw [Kind.ofByte?_byte, Digest.ofBytes?_bytes]
  ofVal_exact := by
    intro v r h
    cases v
    case ref b d =>
      change (match Kind.ofByte? b, Digest.ofBytes? d with
        | some k, some dg => some (AnyRef.mk k dg)
        | _, _ => none) = some r at h
      split at h
      · next k dg hk hd =>
        injection h with h
        subst h
        show Val.ref b d = Val.ref k.byte dg.bytes
        rw [Kind.byte_ofByte? hk, Digest.ofBytes?_exact hd]
      · exact nomatch h
    all_goals exact nomatch h
  fits r := by
    show acceptsIn [] .anyRef (.ref r.kind.byte r.digest.bytes) = true
    simp [acceptsIn, candidates, acceptsAt, Kind.ofByte?_byte, r.digest.length_eq]

/-! ## The node and its codec -/

/-- A node as the store keeps it: the version byte, the kind, the spec (edge 0), the payload as
a value tree. The bytes are `Node.encode`; the address is `sha256` of them. -/
structure Node where
  version : UInt8
  kind : Kind
  spec : Digest
  payload : Val
deriving DecidableEq, Repr

namespace Node

/-- The node bytes of the facts note's Q3: `version ∷ kind ∷ spec ∷ payload`. -/
def encode (n : Node) : Bytes :=
  n.version :: n.kind.byte :: (n.spec.bytes ++ Val.encode n.payload)

/-- The exact reader: version `0`, a registered kind byte, thirty-two spec bytes, then one value
tree and nothing else. -/
def decode : Bytes → Option Node
  | v :: k :: rest =>
    if v = 0 then
      match Kind.ofByte? k, Digest.ofBytes? (rest.take 32), Val.decode (rest.drop 32) with
      | some kind, some spec, some p => some ⟨v, kind, spec, p⟩
      | _, _, _ => none
    else none
  | _ => none

/-- A node is thirty-four header bytes and its payload's frame. -/
theorem length_encode (n : Node) : n.encode.length = 34 + (Val.encode n.payload).length := by
  simp only [encode, List.length_cons, List.length_append, n.spec.length_eq]
  omega

/-- Forward correctness: a version-0 node with a well-formed payload reads back. -/
theorem decode_encode (n : Node) (h : n.payload.WF) (hv : n.version = 0) :
    decode (encode n) = some n := by
  obtain ⟨v, k, spec, p⟩ := n
  change v = 0 at hv
  change p.WF at h
  subst hv
  have ht : (spec.bytes ++ Val.encode p).take 32 = spec.bytes := List.take_left' spec.length_eq
  have hd : (spec.bytes ++ Val.encode p).drop 32 = Val.encode p := List.drop_left' spec.length_eq
  show decode (0 :: k.byte :: (spec.bytes ++ Val.encode p)) = some ⟨0, k, spec, p⟩
  simp only [decode, ht, hd, Kind.ofByte?_byte, Digest.ofBytes?_bytes, Val.decode_encode p h,
    if_true]

/-- Image exactness: whatever reads was those node bytes, with a well-formed payload and
version `0`. The spec's length is carried by `Digest`. -/
theorem decode_exact {b : Bytes} {n : Node} (h : decode b = some n) :
    b = encode n ∧ n.payload.WF ∧ n.version = 0 := by
  match b, h with
  | [], h => exact nomatch h
  | [_], h => exact nomatch h
  | v :: k :: rest, h =>
    simp only [decode] at h
    split at h
    · next hv =>
      split at h
      · next kind spec p hk hs hp =>
        injection h with h
        subst h
        obtain ⟨hb, hwf⟩ := Val.decode_exact hp
        refine ⟨?_, hwf, hv⟩
        show v :: k :: rest = v :: kind.byte :: (spec.bytes ++ Val.encode p)
        rw [Kind.byte_ofByte? hk, Digest.ofBytes?_exact hs, ← hb, List.take_append_drop]
      · exact nomatch h
    · exact nomatch h

/-- One byte string per admissible node: the round trip makes the layout injective. -/
theorem encode_injective {a b : Node} (ha : a.payload.WF) (hb : b.payload.WF)
    (hva : a.version = 0) (hvb : b.version = 0) (h : encode a = encode b) : a = b := by
  have h1 := decode_encode a ha hva
  rw [h, decode_encode b hb hvb] at h1
  injection h1 with h1
  exact h1.symm

end Node

/-! ## The edge scan -/

namespace Val

mutual
/-- The well-formed references of a value tree, in traversal order: every `ref` frame whose kind
byte is registered and whose digest is thirty-two bytes. -/
def refs : Val → List AnyRef
  | .ref b d =>
    match Kind.ofByte? b, Digest.ofBytes? d with
    | Option.some k, Option.some dg => [⟨k, dg⟩]
    | _, _ => []
  | .list xs => refsList xs
  | .pair a b => refs a ++ refs b
  | .some a => refs a
  | .ctor _ args => refsList args
  | _ => []
/-- The references of a list of values, back to back. -/
def refsList : List Val → List AnyRef
  | [] => []
  | x :: xs => refs x ++ refsList xs
end

mutual
/-- Whether some `ref` frame is malformed: an unregistered kind byte, or a digest that is not
thirty-two bytes. Such a frame is refused at admission; it names nothing. -/
def malformedRef : Val → Bool
  | .ref b d => !((Kind.ofByte? b).isSome && decide (d.length = 32))
  | .list xs => malformedRefList xs
  | .pair a b => malformedRef a || malformedRef b
  | .some a => malformedRef a
  | .ctor _ args => malformedRefList args
  | _ => false
/-- `malformedRef` at some member. -/
def malformedRefList : List Val → Bool
  | [] => false
  | x :: xs => malformedRef x || malformedRefList xs
end

end Val

/-- The thirty-two zero bytes: the spec of the genesis node and of nothing else. -/
def zeroDigest : Digest := ⟨List.replicate 32 0, by simp⟩

namespace Node

/-- The references in the payload, traversal order. -/
def refsOf (n : Node) : List AnyRef := n.payload.refs

/-- Whether the payload carries a `ref` frame with a wrong kind byte or length. -/
def malformedRef (n : Node) : Bool := n.payload.malformedRef

/-- Every edge: edge 0 is the spec, at kind `schema`; then the payload's references. -/
def edges (n : Node) : List AnyRef := ⟨.schema, n.spec⟩ :: n.refsOf

/-- The genesis: a schema node with the zero spec. The meta-schema is the one such node the
store admits without resolving its spec edge. -/
def IsGenesis (n : Node) : Prop := n.kind = .schema ∧ n.spec = zeroDigest

instance instDecidableIsGenesis (n : Node) : Decidable n.IsGenesis :=
  inferInstanceAs (Decidable (n.kind = .schema ∧ n.spec = zeroDigest))

/-- The edges admission resolves: every edge, or the payload's references alone for the genesis. -/
def checkedEdges (n : Node) : List AnyRef := if n.IsGenesis then n.refsOf else n.edges

theorem checkedEdges_of_genesis {n : Node} (h : n.IsGenesis) : n.checkedEdges = n.refsOf := by
  unfold checkedEdges
  rw [if_pos h]

theorem checkedEdges_of_not_genesis {n : Node} (h : ¬ n.IsGenesis) : n.checkedEdges = n.edges := by
  unfold checkedEdges
  rw [if_neg h]

/-- Every reference is among the checked edges, genesis or not. -/
theorem mem_checkedEdges_of_mem_refsOf {n : Node} {e : AnyRef} (h : e ∈ n.refsOf) :
    e ∈ n.checkedEdges := by
  unfold checkedEdges
  split
  · exact h
  · exact List.mem_cons_of_mem _ h

end Node

/-! ## The genesis, the spec, the address: under `Content Document` -/

section Genesis

variable [Content Document]

/-- The meta-schema: the document of `Document`'s own shape (Q5). -/
def metaSchema : Document := (shape Document).document

/-- The genesis node: the meta-schema filed as a schema under the zero spec, the one node whose
spec edge admission does not resolve (Q6). -/
def genesisNode : Node := ⟨0, .schema, zeroDigest, toVal metaSchema⟩

/-- The address of the genesis: the spec of every other schema node. -/
def genesisAddress : Digest := sha256 genesisNode.encode

/-- The schema node carrying a document: the genesis for the meta-schema, the genesis's address
as spec for every other document. -/
def schemaNode (d : Document) : Node :=
  ⟨0, .schema, if toVal d = toVal metaSchema then zeroDigest else genesisAddress, toVal d⟩

/-- The spec of a carrier: the address of its shape's document as a schema node. Derived, never
a field (Q3). -/
def specOf (α : Type) [Content α] : Digest := sha256 (schemaNode (shape α).document).encode

/-- The spec a value's node carries: zero exactly for the genesis, `specOf α` for everything else.
The choice is per value because the meta-schema is a `Document` like any other document and
only its own node is the genesis. -/
def specFor {α : Type} [Content α] (a : α) : Digest :=
  if Content.kind α = .schema ∧ toVal a = toVal metaSchema then zeroDigest else specOf α

/-- The node of a carrier: version `0`, its kind, its spec, its value tree. No store is
consulted: a node's bytes are a function of the value alone, so nothing a store later holds — a
trait among it — can move an address. -/
def nodeOf {α : Type} [Content α] (a : α) : Node := ⟨0, Content.kind α, specFor a, toVal a⟩

/-- The address: SHA-256 of the node bytes, typed. -/
def address {α : Type} [Content α] (a : α) : Ref α := ⟨sha256 (nodeOf a).encode⟩

theorem nodeOf_version {α : Type} [Content α] (a : α) : (nodeOf a).version = 0 := rfl

theorem nodeOf_kind {α : Type} [Content α] (a : α) : (nodeOf a).kind = Content.kind α := rfl

theorem nodeOf_payload {α : Type} [Content α] (a : α) : (nodeOf a).payload = toVal a := rfl

theorem address_digest {α : Type} [Content α] (a : α) :
    (address a).digest = sha256 (nodeOf a).encode := rfl

/-- The genesis theorem: the meta-schema fits its own shape. It is the class law `fits` at the
meta-schema, so it holds for every lawful instance the moment one exists. -/
theorem metaSchema_accepts : (shape Document).accepts (toVal metaSchema) = true :=
  fits metaSchema

/-- The meta-schema's schema node is the genesis. -/
theorem schemaNode_metaSchema : schemaNode metaSchema = genesisNode := by
  unfold schemaNode genesisNode
  rw [if_pos rfl]

/-- The spec of `Document` is the genesis's address: `(shape Document).document` is the
meta-schema by definition. -/
theorem specOf_document : specOf Document = genesisAddress := by
  unfold specOf genesisAddress
  rw [show (shape Document).document = metaSchema from rfl, schemaNode_metaSchema]

/-- When `Document` files as `schema`, the meta-schema's node is the genesis. -/
theorem nodeOf_metaSchema (hk : Content.kind Document = .schema) : nodeOf metaSchema = genesisNode := by
  unfold nodeOf genesisNode specFor
  rw [if_pos ⟨hk, rfl⟩, hk]

/-- When `Document` files as `schema`, every document's node is its schema node: the genesis for
the meta-schema, the genesis's address as spec otherwise. -/
theorem nodeOf_document (hk : Content.kind Document = .schema) (d : Document) :
    nodeOf d = schemaNode d := by
  unfold nodeOf schemaNode specFor
  rw [specOf_document]
  by_cases h : toVal d = toVal metaSchema
  · rw [if_pos ⟨hk, h⟩, if_pos h, hk]
  · rw [if_neg (fun hh => h hh.2), if_neg h, hk]

/-! The lattice, proved once over `Content`. -/

theorem address_congr {α : Type} [Content α] {a b : α} (h : a = b) : address a = address b :=
  congrArg address h

/-- Equal node bytes come from equal carriers, when the payloads are well-formed. -/
theorem nodeOf_encode_injective {α : Type} [Content α] {a b : α} (ha : (toVal a).WF)
    (hb : (toVal b).WF) (h : (nodeOf a).encode = (nodeOf b).encode) : a = b := by
  simp only [nodeOf, Node.encode, List.cons.injEq, true_and] at h
  have htail := List.append_inj_right h (by rw [(specFor a).length_eq, (specFor b).length_eq])
  exact Canonical.toVal_injective (Val.encode_injective ha hb htail)

/-- Level 0, no premise about the hash: equal addresses are equal carriers, or two different
node byte strings with one digest — a collision, exhibited. -/
theorem address_eq_or_collision {α : Type} [Content α] {a b : α} (ha : (toVal a).WF)
    (hb : (toVal b).WF) (h : address a = address b) :
    a = b ∨ ((nodeOf a).encode ≠ (nodeOf b).encode ∧
      sha256 (nodeOf a).encode = sha256 (nodeOf b).encode) := by
  have hd : sha256 (nodeOf a).encode = sha256 (nodeOf b).encode := congrArg Ref.digest h
  by_cases he : (nodeOf a).encode = (nodeOf b).encode
  · exact Or.inl (nodeOf_encode_injective ha hb he)
  · exact Or.inr ⟨he, hd⟩

/-- Level 1: under a named injectivity premise for the hash, the address is injective. The
premise is a hypothesis, never an instance. -/
theorem address_inj (hInj : Function.Injective sha256) {α : Type} [Content α] {a b : α}
    (ha : (toVal a).WF) (hb : (toVal b).WF) (h : address a = address b) : a = b :=
  nodeOf_encode_injective ha hb (hInj (congrArg Ref.digest h))

end Genesis

/-- Level 2 is empty: a hash with no injectivity has a collision, exhibited by two different
nodes under the constant hash. -/
example : ∃ n m : Node, n ≠ m ∧ (fun _ => ()) (Node.encode n) = (fun _ => ()) (Node.encode m) :=
  ⟨⟨0, .source, zeroDigest, .unit⟩, ⟨0, .source, zeroDigest, .none⟩,
    (fun h => nomatch (Node.mk.inj h).2.2.2), rfl⟩

/-! ## The layout, guarded: a sample node round-trips, its bytes are the header and the payload,
the refusals are the version, the kind byte, a short spec and a trailing byte. -/

/-- A sample node: the census entry filed as an export under the zero spec. -/
def sampleNode : Node := ⟨0, .«export», zeroDigest, sampleEntry⟩

#guard sampleNode.encode.length = 108
#guard sampleNode.encode.take 2 = [0, 2]
#guard sampleNode.encode.drop 34 = Val.encode sampleEntry
#guard Node.decode sampleNode.encode = some sampleNode
#guard Node.decode (sampleNode.encode ++ [0]) = none
#guard Node.decode (1 :: sampleNode.encode.drop 1) = none
#guard Node.decode (0 :: 16 :: sampleNode.encode.drop 2) = none
#guard Node.decode (0 :: 0 :: sampleNode.encode.drop 2) = none
#guard Node.decode (sampleNode.encode.take 33) = none
#guard Node.decode [] = none
#guard sampleNode.refsOf = []
#guard sampleNode.malformedRef = false
#guard sampleNode.edges = [⟨.schema, zeroDigest⟩]
#guard sampleNode.checkedEdges = sampleNode.edges
#guard (Node.mk 0 .schema zeroDigest sampleEntry).checkedEdges = []
#guard (Val.ref 2 (List.replicate 32 1)).refs = [⟨.«export», ⟨List.replicate 32 1, by simp⟩⟩]
#guard (Val.ref 16 (List.replicate 32 1)).refs = []
#guard (Val.ref 16 (List.replicate 32 1)).malformedRef = true
#guard (Val.ref 2 (List.replicate 31 1)).malformedRef = true
#guard (Val.ctor 0 [.ref 4 (List.replicate 32 7), .nat 3, .some (.ref 6 (List.replicate 32 9))]).refs =
  [⟨.schema, ⟨List.replicate 32 7, by simp⟩⟩, ⟨.annotation, ⟨List.replicate 32 9, by simp⟩⟩]
#guard (Val.ctor 0 [.ref 4 (List.replicate 32 7), .nat 3]).malformedRef = false
-- The typed and untyped reference frames: 42 bytes, `0b … 21 kind digest`; refusals by kind and length.
#guard (Canonical.encode (AnyRef.mk .«export» zeroDigest)).length = 42
#guard (Canonical.encode (AnyRef.mk .«export» zeroDigest)).take 10 = [0x0b, 0, 0, 0, 0, 0, 0, 0, 0x21, 0x02]
#guard Canonical.decode (Canonical.encode (AnyRef.mk .program zeroDigest)) = some (AnyRef.mk .program zeroDigest)
#guard Canonical.decode (α := AnyRef) (Val.encode (.ref 16 zeroDigest.bytes)) = none
#guard Canonical.decode (α := AnyRef) (Val.encode (.ref 2 (List.replicate 31 0))) = none
#guard (Canonical.shape AnyRef).accepts (Canonical.toVal (AnyRef.mk .tree zeroDigest)) = true

/-! ## Receipts -/

#print axioms Ref.ext
#print axioms Ref.instDecidableEq
#print axioms instDecidableEqAnyRef
#print axioms Digest.ofBytes?
#print axioms Digest.ofBytes?_bytes
#print axioms Digest.ofBytes?_exact
#print axioms instCanonicalRef
#print axioms instCanonicalAnyRef
#print axioms instDecidableEqNode
#print axioms Node.encode
#print axioms Node.decode
#print axioms Node.length_encode
#print axioms Node.decode_encode
#print axioms Node.decode_exact
#print axioms Node.encode_injective
#print axioms Val.refs
#print axioms Val.malformedRef
#print axioms zeroDigest
#print axioms Node.refsOf
#print axioms Node.malformedRef
#print axioms Node.edges
#print axioms Node.IsGenesis
#print axioms Node.instDecidableIsGenesis
#print axioms Node.checkedEdges
#print axioms Node.checkedEdges_of_genesis
#print axioms Node.checkedEdges_of_not_genesis
#print axioms Node.mem_checkedEdges_of_mem_refsOf
#print axioms metaSchema
#print axioms genesisNode
#print axioms genesisAddress
#print axioms schemaNode
#print axioms specOf
#print axioms specFor
#print axioms nodeOf
#print axioms address
#print axioms metaSchema_accepts
#print axioms schemaNode_metaSchema
#print axioms specOf_document
#print axioms nodeOf_metaSchema
#print axioms nodeOf_document
#print axioms address_congr
#print axioms nodeOf_encode_injective
#print axioms address_eq_or_collision
#print axioms address_inj
#print axioms sampleNode

end Effect4.Store
