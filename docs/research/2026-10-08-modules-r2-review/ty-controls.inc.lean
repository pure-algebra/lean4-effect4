/-!
Finite review controls for TyModel at 3af74a28.
The runner appends this file to the submitted TyModel declarations.
These controls exercise canonical membership, support and codec admission.
They do not state a new theorem or change a frozen contract.
-/
open TyModel
namespace TyModelReview
structure Unsorted where
  z : Bool
  a : Bool
  deriving DecidableEq, Repr
instance : Modeled Unsorted where
  ty := .record [("z", false, .bool), ("a", false, .bool)]
  toC s := (s.z, (s.a, ()))
  ofC c := ⟨c.1, c.2.1⟩
  to_of := fun (_z, (_a, ())) => rfl
  of_to := fun ⟨_z, _a⟩ => rfl
structure Outer where
  inner : Unsorted
  deriving DecidableEq, Repr
derive_modeled Outer

def raw : Unsorted := ⟨true, false⟩
def outer : Outer := ⟨raw⟩
#eval refusal (Modeled.ty (α := Outer))
#eval ((Modeled.image Outer).ofVal ((Modeled.image Outer).toVal outer)) == some outer
#eval Val.hasTy ((Modeled.image Outer).toVal outer) (Modeled.ty (α := Outer)) []
#eval (Effect4.Schema.encode (Modeled.ty (α := Outer)) ((Modeled.image Outer).toVal outer)).isSome

-- Unsupported nested fields do not stop construction of Modeled or its image.
instance : Modeled Empty where
  ty := .handle "Unimplemented.Identity"
  toC x := x
  ofC x := x
  to_of := fun _ => rfl
  of_to := fun _ => rfl
structure Unsupported where
  values : List Empty

derive_modeled Unsupported
#eval refusal (Modeled.ty (α := Unsupported))
#eval ((Modeled.image Unsupported).ofVal ((Modeled.image Unsupported).toVal ⟨[]⟩)).isSome

-- All Nat values have an exact image and membership; JSON admission is value-specific.
#eval Val.hasTy ((Modeled.image Nat).toVal (2^53+1)) (Modeled.ty (α := Nat)) []
#eval (Effect4.Schema.encode (Modeled.ty (α := Nat)) ((Modeled.image Nat).toVal (2^53+1))).isSome

structure Renamed where
  original : Bool
  deriving DecidableEq, Repr
derive_modeled Renamed (misspelled := "changed")
#eval Modeled.ty (α := Renamed) == .record [("original", false, .bool)]
end TyModelReview

-- Exact record encoding alone does not provide the machine's canonical write law.
#guard TyModel.refusal (.record [("z", false, .nat), ("a", false, .nat)]) == none
#guard Machine.Record.set
    ((TyModel.image (.record [("z", false, .nat), ("a", false, .nat)])).toVal
      ((1 : Nat), ((2 : Nat), ())))
    "z" (.nat 3) !=
  some ((TyModel.image (.record [("z", false, .nat), ("a", false, .nat)])).toVal
    ((3 : Nat), ((2 : Nat), ())))

-- A lawful derived positive control does satisfy all three checks on this sample.
structure Ordinary where
  z : Bool
  a : Bool
  deriving DecidableEq
derive_modeled Ordinary
#guard TyModel.refusal (Modeled.ty (α := Ordinary)) == none
#guard ((Modeled.image Ordinary).ofVal ((Modeled.image Ordinary).toVal ⟨true, false⟩)) ==
  some (⟨true, false⟩ : Ordinary)
#guard Val.hasTy ((Modeled.image Ordinary).toVal ⟨true, false⟩) (Modeled.ty (α := Ordinary)) []
#guard (Effect4.Schema.encode (Modeled.ty (α := Ordinary))
  ((Modeled.image Ordinary).toVal ⟨true, false⟩)).isSome

-- Positive codec control beside the large-Nat refusal.
#guard (Effect4.Schema.encode (Modeled.ty (α := Nat)) ((Modeled.image Nat).toVal 7)).isSome
