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
-- Expected failure: checked generation uses decide rather than the field instance's checked proof.
derive_modeled Holder
end L1OpaqueControl
