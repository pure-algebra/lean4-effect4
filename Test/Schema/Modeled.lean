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
/-- error: derive_modeled: field type Int has no Modeled instance -/
#guard_msgs in
structure Holder where
  stamp : Int
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

end Test.Schema.Modeled.Controls
