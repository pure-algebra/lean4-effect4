import Effect4.Schema.Fold
import Effect4.Schema.Authoring

/-!
# Schema templates: Schema IR with holes, filled by a fold over the Schema AST

A per-constructor table's Schema column (decisions row 182 (a), slice C) holds, for each
constructor of a family, its node of rc.112's Schema IR: a `Representation` whose references
`effect4/child/i` stand for the node's children (in declaration order) and whose reserved string
`effect4/leaf` stands for its payload, at a declaration's id or as a string literal. Any Schema node
can appear in a row: a declaration's argument order, its constant slots and a number's checks are
written as the IR writes them, not as special forms beside it.

Filling a template is a fold over the Schema AST (`cata_representation`): the generated identity
algebra (`RepresentationAlgebra.id`) with three arms changed. A child reference resolves to that
child's representation, and the payload mark at a declaration's id or in a string literal becomes
the payload. Every other node is rebuilt as it is (`cata_id_representation`). A reference to no
child stays a reference, so a template's own `$ref`s pass through.
-/

set_option autoImplicit false

namespace Effect4.Schema.Template

open Effect4

/-- The reference a template writes for the node's `i`-th child. -/
def childRef (i : Nat) : ReferenceKey := ⟨"effect4/child/" ++ toString i⟩

/-- A template's `i`-th child. -/
abbrev child (i : Nat) : Representation := .reference (childRef i)

/-- The string a template writes where the node's payload goes. -/
def leafMark : String := "effect4/leaf"

/-- The child a reference names, counting from `i`: the first child whose reference it is. -/
def lookupChild (r : ReferenceKey) : List Representation → Nat → Option Representation
  | [], _ => none
  | k :: ks, i => if r = childRef i then some k else lookupChild r ks (i + 1)

/-- A declaration's annotation with the payload at the mark. -/
def fillAnnotation (leaf : Option String) (a : RepresentationAnnotation) : RepresentationAnnotation :=
  match leaf with
  | some s => if a.id = leafMark then { a with id := s } else a
  | none => a

/-- A literal with the payload at the mark. -/
def fillLiteral (leaf : Option String) (v : LiteralValue) : LiteralValue :=
  match leaf, v with
  | some s, .string m => if m = leafMark then .string s else v
  | _, _ => v

/-- The fill's algebra: the identity on the Schema AST, but at the holes. -/
def fillAlg (leaf : Option String) (kids : List Representation) :
    RepresentationAlgebra RepresentationSelfCarrier :=
  { RepresentationAlgebra.id with
    representation_reference := fun r => (lookupChild r kids 0).getD (.reference r)
    representation_declaration := fun a0 a1 a2 a3 => .declaration (fillAnnotation leaf a0) a1 a2 a3
    representation_literal := fun a0 a1 a2 => .literal a0 a1 (fillLiteral leaf a2) }

/-- **A template filled**: the fold over the Schema AST with the fill's algebra. -/
def fill (tmpl : Representation) (leaf : Option String) (kids : List Representation) :
    Representation :=
  cata_representation (fillAlg leaf kids) tmpl

end Effect4.Schema.Template
