/-! A one-parameter structure holding a child and two distinct payloads, under a list.
The ordinary fold generates its map; extras must check and reuse that map. -/
set_option autoImplicit false
universe u
namespace GenFix.Structure
structure ElemOf (α : Type u) where
  isOptional : Bool
  type : α
  note : String
inductive Tree where
  | leaf
  | node (fields : List (ElemOf Tree))
end GenFix.Structure
