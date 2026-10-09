import Effect4.Schema.Modeled.Derive
import Effect4.Laws.Schema.Modeled
open Effect4.Program Effect4.Schema
namespace L1OpaqueControl
structure Flag where
  value : Bool
opaque flagModel : Modeled Flag := {
  ty := .bool
  checked := rfl
  toC := fun x => x.value
  ofC := fun x => ⟨x⟩
  to_of := fun _ => rfl
  of_to := fun ⟨_⟩ => rfl
}
attribute [instance] flagModel
-- A valid instance inherits the law without reducing its implementation.
example (x : Flag) : Val.hasTy ((Modeled.image Flag).toVal x)
    (Modeled.ty (α := Flag)) [] = true := Modeled.member Flag x []
structure Holder where
  flag : Flag
def Holder.modeledTy : Ty := .record [("flag", false, Modeled.ty (α := Flag))]
instance : Modeled Holder where
  ty := Holder.modeledTy
  checked := by
    change (if Effect4.Field.Ascending Effect4.Field.bytesKey
      [("flag", false, Model.refusal (Modeled.ty (α := Flag)))] then
      (Model.refusal (Modeled.ty (α := Flag))).or none else
      some "record fields out of canonical order") = none
    have order : Effect4.Field.Ascending Effect4.Field.bytesKey
        [("flag", false, Model.refusal (Modeled.ty (α := Flag)))] := by decide
    rw [if_pos order, Modeled.checked (α := Flag)]
    rfl
  toC := fun s => (Modeled.toC s.flag, ())
  ofC := fun c => ⟨Modeled.ofC c.1⟩
  to_of := fun (x, ()) => Prod.ext (Modeled.to_of x) rfl
  of_to := fun ⟨x⟩ => congrArg Holder.mk (Modeled.of_to x)
example (x : Holder) : Val.hasTy ((Modeled.image Holder).toVal x)
    (Modeled.ty (α := Holder)) [] = true := Modeled.member Holder x []
end L1OpaqueControl
