import ProbeU.Generic
import Effect4.Schema.Bridge

/-!
# Probe U — the spelling table of `Ty` (family (c)): one row per constructor, three faces

The per-constructor data three hand traversals restate today — `Ty.renderRaw` (TypeScript
text, `Program/Ty.lean:95`), `Bridge.schema` (rc.112's `SchemaRepresentation`,
`Schema/Bridge.lean:37`) and `Ty.key` (the structural key whose codes are the wire tags,
`Program/Ty.lean:146`, `tools/Effect4Gen/wire-tags.json`) — written once as a table, and one
generic interpreter per face. The table is what the generator would read (a JSON row per
constructor) and emit; here it is written in the emitted form. A new constructor is a
missing field of `tyFaces` and so a compile error here, at the one place its spellings are
decided; the folds themselves never change.

The table itself is data: `U/tables/ty-faces.json`, emitted as `tyFaces` by the table emitter
(`U/patches/TableGen.lean`) into `U/generated/ProbeU/FacesTable.lean`. The agreement of each
generic fold with today's hand definition is proved in `U/probes/SpellingFolds.lean` from the
generated uniqueness theorem.
-/

set_option autoImplicit false

namespace ProbeU

open Effect4 Effect4.Program

/-! ## The TypeScript face: a template per constructor -/

/-- One piece of a constructor's spelling: literal text, the folded child at a position, or
the node's own payload. -/
inductive Piece where
  | text (s : String)
  | child (i : Nat)
  | leaf
deriving DecidableEq, Repr

/-- A constructor's spelling, left to right. -/
abbrev Spell := List Piece

/-- A piece, rendered against the node's payload text and its folded children. -/
def Piece.render (leaf : String) (kids : List String) : Piece → String
  | .text s => s
  | .child i => kids.getD i ""
  | .leaf => leaf

/-- A spelling, rendered left-nested (`((p₀ ++ p₁) ++ p₂) …`), which is how the hand arms
associate. -/
def Spell.render (p : Spell) (leaf : String) (kids : List String) : String :=
  match p with
  | [] => ""
  | p0 :: rest => rest.foldl (fun acc q => acc ++ q.render leaf kids) (p0.render leaf kids)

/-- The payload as TypeScript text: a host spelling verbatim, a literal's value, a template
parameter as `A`, `E`, then `T2`, `T3`, … -/
def tsLeaf : TyLeaf → String
  | .none => ""
  | .str s => s
  | .nat 0 => "A"
  | .nat 1 => "E"
  | .nat n => "T" ++ toString n

/-! ## The Schema face -/

/-- A constructor's `SchemaRepresentation`: a constant node, a declaration named by the payload,
a literal of the payload, an rc.112 declaration with its parameters in a stated order and
constant extra slots, an array, a two-element tuple, or an `anyOf` union. -/
inductive SchemaSpell where
  | const (r : Representation)
  | declLeaf
  | literalLeaf
  | decl (id : String) (perm : List Nat) (extras : List Representation)
  | array
  | tuple
  | union

/-- The Schema node of a constructor, against its payload and folded children. -/
def SchemaSpell.render : SchemaSpell → TyLeaf → List Representation → Representation
  | .const r, _, _ => r
  | .declLeaf, .str s, _ => .declaration ⟨s, .null⟩ none [] []
  | .declLeaf, _, _ => Schema.never
  | .literalLeaf, .str s, _ => Schema.literalString s
  | .literalLeaf, _, _ => Schema.never
  | .decl id perm extras, _, kids =>
    .declaration ⟨id, .null⟩ none (perm.map (fun i => kids.getD i Schema.never) ++ extras) []
  | .array, _, kids => Schema.array (kids.getD 0 Schema.never)
  | .tuple, _, kids =>
    Schema.tuple [Schema.element (kids.getD 0 Schema.never), Schema.element (kids.getD 1 Schema.never)]
  | .union, _, kids => .union none [] [kids.getD 0 Schema.never, kids.getD 1 Schema.never] .anyOf

/-! ## The key face: a code per constructor, the payload's bytes, the children length-prefixed -/

/-- The payload as key digits: a string by its UTF-8 bytes, an index as itself. -/
def keyLeaf : TyLeaf → List Nat
  | .none => []
  | .str s => s.toUTF8.data.toList.map UInt8.toNat
  | .nat n => [n]

/-- Every child but the last length-prefixed, the last as it is: a prefix code. -/
def prefixed : List (List Nat) → List Nat
  | [] => []
  | [k] => k
  | k :: ks => k.length :: (k ++ prefixed ks)

/-- One node's key from its code, payload and children's keys. -/
def keyNode (code : Nat) (leaf : TyLeaf) (kids : List (List Nat)) : List Nat :=
  match kids with
  | [] => code :: keyLeaf leaf
  | _ => code :: (keyLeaf leaf ++ prefixed kids)

/-! ## The table -/

/-- One constructor's spellings, one column per face. -/
structure FaceRow where
  ts : Spell
  schema : SchemaSpell
  code : Nat

/-- An Effect module type `M.M<…>` on the TypeScript face (the arguments in `perm`'s order). -/
def moduleTs (head : String) (perm : List Nat) : Spell :=
  match perm with
  | [] => [.text head]
  | i :: rest =>
    [.text (head ++ "<"), .child i] ++ rest.flatMap (fun j => [.text ", ", .child j]) ++ [.text ">"]

/-! ## The three folds: one generic definition each, the table their only input -/

/-- TypeScript text. -/
def tsAlg (tbl : TyTable FaceRow) : TyAlgebra (fun _ => String) :=
  TyAlgebra.ofLayer fun c l kids => (tbl.get c).ts.render (tsLeaf l) kids

/-- The Schema node. -/
def schemaAlg (tbl : TyTable FaceRow) : TyAlgebra (fun _ => Representation) :=
  TyAlgebra.ofLayer fun c l kids => (tbl.get c).schema.render l kids

/-- The structural key. -/
def keyAlg (tbl : TyTable FaceRow) : TyAlgebra (fun _ => List Nat) :=
  TyAlgebra.ofLayer fun c l kids => keyNode (tbl.get c).code l kids

end ProbeU
