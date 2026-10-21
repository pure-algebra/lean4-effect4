import Lean
import OCaml5.Ml.Syntax
import OCaml5.Lcnf.TypeRows

/-! The native constructor table owns names once: the constructors of the types the route spells
as OCaml's own datatypes (list, option, bool, tuple, result, unit), and `Nat`'s two, whose values
are Zarith's `Z.t`, spelled by the `Nat` row (`OCaml5.Lcnf.natLiteral`, `natSucc`). Construction and matching use the same shape; `matchable` says which types OCaml
matches on, and the type annotation policy derives its owner set from this table. It is one of
the owners `OCaml5.Lcnf.nativeOwner?` reads. -/
namespace OCaml5.Lcnf.Native
open Lean
inductive Shape where
  | nil | cons | none | some | true | false | pair | ok | error | unit | zero | succ
  deriving Inhabited

structure Rule where
  owner : Name
  constructor : Name
  shape : Shape

def rules : Array Rule := #[
  ⟨``List, ``List.nil, .nil⟩, ⟨``List, ``List.cons, .cons⟩,
  ⟨``Option, ``Option.none, .none⟩, ⟨``Option, ``Option.some, .some⟩,
  ⟨``Bool, ``Bool.true, .true⟩, ⟨``Bool, ``Bool.false, .false⟩,
  ⟨``Prod, ``Prod.mk, .pair⟩, ⟨``Except, ``Except.ok, .ok⟩,
  ⟨``Except, ``Except.error, .error⟩, ⟨``PUnit, ``PUnit.unit, .unit⟩,
  ⟨``Nat, ``Nat.zero, .zero⟩, ⟨``Nat, ``Nat.succ, .succ⟩]

def owns (name : Name) : Bool := name == ``Unit || rules.any (·.owner == name)

/-- The types OCaml matches on directly: every constructor is one of OCaml's own, as a pattern
too. `Nat` is owned for its two constructors' values only: Zarith's `Z.t` has no constructor to
match, and Lean's compiler takes a natural apart by comparison. -/
def matchable (name : Name) : Bool := owns name && name != ``Nat
def find? (name : Name) : Option Shape := (rules.find? (·.constructor == name)).map (·.shape)

def expression (name : Name) (args : List Ml.Expr) : Option Ml.Expr := do
  match ← find? name, args with
  | .nil, [] => return Ml.Expr.nil
  | .cons, [h, t] => return .binop "::" h t
  | .none, [] => return Ml.Expr.none_
  | .some, [x] => return Ml.Expr.some_ x
  | .true, [] => return .bool true
  | .false, [] => return .bool false
  | .pair, [a, b] => return .tuple [a, b]
  | .ok, [x] => return .ctor "Ok" [x]
  | .error, [x] => return .ctor "Error" [x]
  | .unit, [] => return .unit
  | .zero, [] => return OCaml5.Lcnf.natLiteral 0
  | .succ, [x] => return OCaml5.Lcnf.natSucc x
  | _, _ => none

def pattern (name : Name) (args : List Ml.Pat) : Option Ml.Pat := do
  match ← find? name, args with
  | .nil, [] => return Ml.Pat.nil
  | .cons, [h, t] => return .cons h t
  | .none, [] => return Ml.Pat.none_
  | .some, [x] => return Ml.Pat.some_ x
  | .true, [] => return Ml.Pat.true_
  | .false, [] => return Ml.Pat.false_
  | .pair, [a, b] => return .tuple [a, b]
  | .ok, [x] => return .ctor "Ok" [x]
  | .error, [x] => return .ctor "Error" [x]
  | .unit, [] => return Ml.Pat.unit
  | _, _ => none
end OCaml5.Lcnf.Native
