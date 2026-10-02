import GenFix.Structure.Extras
set_option autoImplicit false
namespace GenFix.Structure

def specimen : Tree := .node [⟨true, .leaf, "first"⟩,
  ⟨false, .node [⟨true, .leaf, "inner"⟩], "second"⟩,
  ⟨true, .leaf, "third"⟩]

def spell : TreeCtor → List (TreeArgF String) → String
  | .leaf, _ => "leaf"
  | .node, [.list_elemOf_tree fields] => String.intercalate ";" (fields.map fun e =>
      e.note ++ (if e.isOptional then "?" else "!") ++ "(" ++ e.type ++ ")")
  | _, _ => "malformed"

#guard cata_tree (TreeAlgebra.ofLayer spell) specimen =
  "first?(leaf);second!(inner?(leaf));third?(leaf)"
#guard (treeShape specimen).flatMap (fun
  | .list_elemOf_tree fields => fields.map fun e => (e.note, e.isOptional)) =
  [("first", true), ("second", false), ("third", true)]
#guard (treeKids specimen).length = 3

def allGood (_ : TreeCtor) (args : List (TreeArgF Bool)) : Bool :=
  (args.flatMap TreeArgF.kids).all id

theorem allGood_true (t : Tree) : cata_tree (TreeAlgebra.ofLayer allGood) t = true :=
  cata_ofLayer_inv allGood (· = true) (fun _ args h => by
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
    exact h a ha b hb) t

#print axioms allGood_true
end GenFix.Structure
