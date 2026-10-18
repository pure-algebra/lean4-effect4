import Effect4.Store.Domain.Cas
import Effect4.Store.Domain.Genesis
import TestSupport.CasEntry

/-!
# Typed store read controls

These finite cases exercise byte diagnostics and typed reading through `Cas.get`.
The fixture replay deliberately files a supplied node at a fixed address.
That replay tests read refusal; it claims no admitted-store or hash invariant.
`Cas.get_exact` is read at the concrete entry carrier below.
-/

set_option autoImplicit false
namespace Test.Store.TypedReadControls
open Effect4 Effect4.Store
open Effect4.Store.Templates

private def sameResult {E A : Type} [DecidableEq E] [DecidableEq A]
    (left right : Except E A) : Bool :=
  match left, right with
  | .ok a, .ok b => decide (a = b)
  | .error a, .error b => decide (a = b)
  | _, _ => false

/-- A fixed-address fixture exposes each typed header check independently. -/
def readEntry (node : Node) : Except ReadRefusal Entry :=
  match CasOf.ofReplay (fun _ => .ok ⟨[(zeroDigest, node)], []⟩) [] with
  | .error _ => .error .payload
  | .ok cas => Cas.get cas ⟨zeroDigest⟩

#guard sameResult (readEntry (nodeOf entry)) (.ok entry)
#guard sameResult (readEntry { nodeOf entry with version := 1, kind := .tree, spec := zeroDigest, payload := .nat 0 }) (.error (.version 1))
#guard sameResult (readEntry { nodeOf entry with kind := .tree, spec := zeroDigest, payload := .nat 0 }) (.error (.kind .«export» .tree))
#guard sameResult (readEntry { nodeOf entry with spec := zeroDigest, payload := .nat 0 }) (.error .spec)
#guard sameResult (readEntry { nodeOf entry with payload := .nat 0 }) (.error .payload)

-- The retired reader accepts this payload despite its wrong version and spec.
#guard (let bad := { nodeOf entry with version := 1, spec := zeroDigest }
  if bad.kind = Content.kind Entry then Canonical.ofVal (α := Entry) bad.payload else none) = some entry
#guard sameResult (readEntry { nodeOf entry with version := 1, spec := zeroDigest }) (.error (.version 1))

-- The genesis has a per-value zero spec. A universal specOf check would refuse it.
#guard (Node.readContent (α := Document) genesisNode).toOption = some metaSchema
#guard genesisNode.spec = zeroDigest
#guard specOf Document ≠ zeroDigest

-- Header checks precede spec length and payload checks.
#guard sameResult (Node.read [1, 127]) (.error (.badVersion 1))
#guard sameResult (Node.read [0, 127]) (.error (.unregisteredKind 127))
#guard sameResult (Node.read [0, 4]) (.error .shortSpec)
#guard sameResult (Node.read []) (.error .shortSpec)
#guard sameResult (Node.read [0]) (.error .shortSpec)

/-- Small valid node bytes avoid a schema-size dependency in raw-byte controls. -/
def raw : Node := ⟨0, .schema, zeroDigest, .nat 1⟩
#guard sameResult (Node.read raw.encode) (.ok raw)
#guard sameResult (Node.read (raw.encode ++ [0])) (.error .trailing)
#guard sameResult (Node.read raw.encode.dropLast) (.error .badFrame)
#guard sameResult (Node.read (0 :: 4 :: (zeroDigest.bytes ++ framed 253 []))) (.error (.unknownTag 253))
#guard sameResult (Node.read (0 :: 4 :: (zeroDigest.bytes ++ framed Tag.list (framed 253 [])))) (.error (.unknownTag 253))
#guard sameResult (Node.read (0 :: 4 :: (zeroDigest.bytes ++ framed Tag.bytes (framed 253 []))))
  (.ok ⟨0, .schema, zeroDigest, .bytes (framed 253 [])⟩)

-- A successful typed read names the exact stored entry, including its spec and version.
example {replay : List Event → Except TxnRefusal Store} {cas : CasOf replay}
    {ref : Ref Entry} {value : Entry} (h : Cas.get cas ref = .ok value) :
    cas.store.find ref.digest = some (nodeOf value) :=
  Cas.get_exact h

end Test.Store.TypedReadControls
