import Effect4.Schema.Modeled.Derive
import Effect4.Laws.Schema.Modeled

/-! The battery of `Modeled` (decisions row 330, slice L1): an ordinary nested record derived,
the two laws read at it, and one red control for each premise of the instance and the deriving
step. -/

set_option autoImplicit false

open Effect4.Program Effect4.Schema

namespace Test.Schema.Modeled

structure Waiter where
  id : Nat
  hint : Nat
  deriving Modeled, DecidableEq, Repr

structure LatchCell where
  waiters : List Waiter
  isOpen : Bool
  label : Option String
  deriving DecidableEq, Repr

derive_modeled LatchCell (isOpen := "open")

def cell : LatchCell := ⟨[⟨4, 5⟩], false, some "gate"⟩

-- Reader: every cell value inhabits the derived type at every allocation table, with no proof
-- of its own.
example (c : LatchCell) (alloc : List String) :
    Val.hasTy ((Modeled.image LatchCell).toVal c) (Modeled.ty (α := LatchCell)) alloc = true :=
  Modeled.member LatchCell c alloc

-- Reader: the cell survives JSON and back; its codec premise is decided at the value.
example : ((encode (CTy.ofRaw (Modeled.ty (α := LatchCell))).toRaw
      ((Modeled.image LatchCell).toVal cell)).bind
      (decode (CTy.ofRaw (Modeled.ty (α := LatchCell))).toRaw)).bind
      (Modeled.image LatchCell).ofVal = some cell :=
  Modeled.codec_roundtrip LatchCell cell (by decide)

-- The derived type: fields in canonical order, under their spellings.
#guard Modeled.ty (α := LatchCell) == .record [("label", false, .option .string),
  ("open", false, .bool),
  ("waiters", false, .list (.record [("hint", false, .nat), ("id", false, .nat)]))]
-- The cell's value is the machine's record frame, in that order.
#guard (Modeled.image LatchCell).toVal cell ==
  .ctor 0 [.list [.str "label", .str "open", .str "waiters"],
    .list [.some (.str "gate"), .bool false,
      .list [.ctor 0 [.list [.str "hint", .str "id"], .list [.nat 5, .nat 4]]]]]

-- Control: the codec premise is false for a natural above 2^53, which inhabits `nat`.
#guard !Ty.isCodecValue (CTy.ofRaw (Modeled.ty (α := Nat))).toRaw
  ((Modeled.image Nat).toVal (2^53 + 1))

end Test.Schema.Modeled

/-! ## Red controls: each premise of an instance and of the deriving step, refused -/

namespace Test.Schema.Modeled.Controls

structure Unsorted where
  z : Bool
  a : Bool

-- A hand instance whose record names are out of canonical order: its check fails. An
-- `example` adds no declaration, so the failed proof leaves nothing behind.
/--
error: Tactic `decide` proved that the proposition
  Model.refusal (Ty.record [("z", false, Ty.bool), ("a", false, Ty.bool)]) = none
is false
-/
#guard_msgs in
example : Modeled Unsorted where
  ty := .record [("z", false, .bool), ("a", false, .bool)]
  checked := by decide
  toC s := (s.z, (s.a, ()))
  ofC c := ⟨c.1, c.2.1⟩
  to_of := fun (_, (_, ())) => rfl
  of_to := fun ⟨_, _⟩ => rfl

-- A hand instance at an identity type: its check fails, since an identity needs its table.
/--
error: Tactic `decide` proved that the proposition
  Model.refusal (Ty.handle "Unimplemented.Identity") = none
is false
-/
#guard_msgs in
example : Modeled Empty where
  ty := .handle "Unimplemented.Identity"
  checked := by decide
  toC x := x.elim
  ofC x := x
  to_of := fun x => x.elim
  of_to := fun x => x.elim

structure Renamed where
  original : Bool

-- A rename of a field that does not exist.
/-- error: derive_modeled: Test.Schema.Modeled.Controls.Renamed has no field misspelled -/
#guard_msgs in
derive_modeled Renamed (misspelled := "changed")

structure TwoFlags where
  left : Bool
  right : Bool

-- Two fields under one spelling.
/-- error: derive_modeled: two fields of Test.Schema.Modeled.Controls.TwoFlags are spelled flag -/
#guard_msgs in
derive_modeled TwoFlags (left := "flag") (right := "flag")

-- One field renamed twice.
/-- error: derive_modeled: field left is renamed twice -/
#guard_msgs in
derive_modeled TwoFlags (left := "a") (left := "b")

structure Boxed (α : Type) where
  value : α

-- A structure with a parameter.
/--
error: derive_modeled: Test.Schema.Modeled.Controls.Boxed has parameters; the first profile is monomorphic
-/
#guard_msgs in
derive_modeled Boxed

structure Lifted.{u} where
  value : ULift.{u} Nat

-- A structure with a universe parameter.
/--
error: derive_modeled: Test.Schema.Modeled.Controls.Lifted has universe parameters; the first profile is monomorphic
-/
#guard_msgs in
derive_modeled Lifted

-- A field type with no instance, through the deriving handler.
/-- error: derive_modeled: field type Float has no Modeled instance -/
#guard_msgs in
structure Holder where
  stamp : Float
  deriving Modeled

structure Proved where
  fact : True

-- A field that is a proof.
/-- error: derive_modeled: field type True is a proposition -/
#guard_msgs in
derive_modeled Proved

structure Sized where
  n : Nat
  items : Fin n

-- A field whose type depends on another field.
/-- error: derive_modeled: field type Fin n depends on another field -/
#guard_msgs in
derive_modeled Sized

structure Token where
  value : Bool

def Token.modeledTy : Nat := 0

-- A generated name that already exists: one refusal, and nothing written.
/-- error: derive_modeled: Test.Schema.Modeled.Controls.Token.modeledTy already exists -/
#guard_msgs in
derive_modeled Token

/-- error: Unknown constant `Test.Schema.Modeled.Controls.Token.modeled_checked` -/
#guard_msgs in
#check Token.modeled_checked

end Test.Schema.Modeled.Controls

/-! ## A field instance may be opaque: deriving uses its contract alone -/

namespace Test.Schema.Modeled.Opaque

structure Flag where
  value : Bool

opaque flagModeled : Modeled Flag := {
  ty := .bool
  checked := rfl
  toC := fun x => x.value
  ofC := fun x => ⟨x⟩
  to_of := fun _ => rfl
  of_to := fun ⟨_⟩ => rfl }

attribute [instance] flagModeled

structure Holder where
  flag : Flag
  count : Nat
  deriving Modeled

-- Reader: every holder inhabits its derived type, with the field instance kept opaque.
example (h : Holder) (alloc : List String) :
    Val.hasTy ((Modeled.image Holder).toVal h) (Modeled.ty (α := Holder)) alloc = true :=
  Modeled.member Holder h alloc

end Test.Schema.Modeled.Opaque

/-! ## Sum types, integers and literals (the types audit, §6.5)

`deriving Modeled` on an inductive writes a union of one `_tag` record per constructor, the
constructor's name its tag (Probe T: rc.112's `Data.TaggedEnum`); an inductive with no field
writes a union of string literals. An integer is its `nat` or `negInt` frame. -/

namespace Test.Schema.Modeled.Sums

inductive Shape where
  | circle (radius : Nat)
  | square (side : Nat) (label : String)
  | dot
  deriving Modeled, DecidableEq

-- Finite evaluation: the type, each record in canonical field order.
#guard Modeled.ty (α := Shape) ==
  .union (.record [("_tag", false, .lit "circle"), ("radius", false, .nat)])
    (.union (.record [("_tag", false, .lit "square"), ("label", false, .string),
        ("side", false, .nat)])
      (.record [("_tag", false, .lit "dot")]))
-- Finite evaluation: a value's image is the record of its constructor, and it reads back.
#guard (Modeled.image Shape).toVal (.square 2 "a") ==
  .ctor 0 [.list [.str "_tag", .str "label", .str "side"], .list [.str "square", .str "a", .nat 2]]
#guard [Shape.circle 1, .square 2 "a", .dot].all fun s =>
  (Modeled.image Shape).ofVal ((Modeled.image Shape).toVal s) == some s
-- Reader: every shape inhabits the derived union, with no proof of its own.
example (s : Shape) (alloc : List String) :
    Val.hasTy ((Modeled.image Shape).toVal s) (Modeled.ty (α := Shape)) alloc = true :=
  Modeled.member Shape s alloc

-- Two constructors with the same field names are told apart by their `_tag` column alone.
inductive Move where
  | left (steps : Nat)
  | right (steps : Nat)
  deriving Modeled, DecidableEq

#guard [Move.left 3, .right 3].all fun m =>
  (Modeled.image Move).ofVal ((Modeled.image Move).toVal m) == some m

-- An inductive with no field is a union of string literals, rc.112's literal enum.
inductive Color where
  | red | green | blue
  deriving Modeled, DecidableEq

#guard Modeled.ty (α := Color) == .union (.lit "red") (.union (.lit "green") (.lit "blue"))
#guard (Modeled.image Color).toVal .green == .str "green"
#guard (Modeled.image Color).ofVal (.str "blue") == some .blue
-- Control: a string outside the enum reads as nothing.
#guard (Modeled.image Color).ofVal (.str "purple") == none

-- An integer field, negative or not.
structure Account where
  owner : String
  balance : Int
  deriving Modeled, DecidableEq

#guard (Modeled.image Account).toVal ⟨"ada", -3⟩ ==
  .ctor 0 [.list [.str "balance", .str "owner"], .list [.negInt 2, .str "ada"]]
#guard [Account.mk "ada" (-3), ⟨"bob", 4⟩].all fun a =>
  (Modeled.image Account).ofVal ((Modeled.image Account).toVal a) == some a

-- A sum type as a field of a structure, and a structure inside a constructor.
structure Drawing where
  shapes : List Shape
  owner : Account
  deriving Modeled

example (d : Drawing) (alloc : List String) :
    Val.hasTy ((Modeled.image Drawing).toVal d) (Modeled.ty (α := Drawing)) alloc = true :=
  Modeled.member Drawing d alloc

end Test.Schema.Modeled.Sums

namespace Test.Schema.Modeled.SumControls

/-- error: derive_modeled: a field of Test.Schema.Modeled.SumControls.Unnamed.wrap has no name; name each field -/
#guard_msgs in
inductive Unnamed where
  | wrap : Nat → Unnamed
  deriving Modeled

/-- error: derive_modeled: Test.Schema.Modeled.SumControls.Tree is recursive; a value type has no recursion -/
#guard_msgs in
inductive Tree where
  | leaf
  | node (left right : Tree)
  deriving Modeled

/-- error: derive_modeled: Test.Schema.Modeled.SumControls.Tagged.mark has a field named _tag, which its tag takes -/
#guard_msgs in
inductive Tagged where
  | mark (_tag : String)
  deriving Modeled

end Test.Schema.Modeled.SumControls
