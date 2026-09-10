import Effect4.Laws.Program.TypeAlgebra
import Effect4.Store.Image.Containers

/-!
Compositional models of program values. The existing Image owns encoding and exact decoding;
CTy owns normalization. Allocation assumptions depend on the actual value, so a handle model
need not claim that a finite allocation table admits every possible handle index.
-/
namespace Effect4.Program
open Store

structure ValueModel (α : Type) where
  image : Image α
  type : CTy
  needs : List String → α → Prop
  member : ∀ allocated value, needs allocated value →
    Val.hasTy (image.toVal value) type.toRaw allocated = true

namespace ValueModel
variable {α β : Type}

/-- Attach the existing membership-normalization theorem to an image's supplied law. -/
def ofImage (image : Image α) (raw : Ty) (needs : List String → α → Prop)
    (member : ∀ allocated value, needs allocated value →
      Val.hasTy (image.toVal value) raw allocated = true) : ValueModel α where
  image
  type := CTy.ofRaw raw
  needs
  member allocated value h := by
    change Val.hasTy (image.toVal value) raw.normalize allocated = true
    rw [hasTy_normalize]
    exact member allocated value h

def nat : ValueModel Nat := ofImage Image.nat .nat (fun _ _ => True) (fun _ _ _ => rfl)
def bool : ValueModel Bool := ofImage Image.bool .bool (fun _ _ => True) (fun _ _ _ => rfl)
def string : ValueModel String := ofImage Image.string .string (fun _ _ => True) (fun _ _ _ => rfl)

def option (model : ValueModel α) : ValueModel (Option α) :=
  ofImage (Image.option model.image) (.option model.type.toRaw)
    (fun allocated value => match value with | none => True | some a => model.needs allocated a)
    (by
      intro allocated value h
      cases value with
      | none => rfl
      | some a => exact model.member allocated a h)

def list (model : ValueModel α) : ValueModel (List α) :=
  ofImage (Image.list model.image) (.list model.type.toRaw)
    (fun allocated values => ∀ a ∈ values, model.needs allocated a)
    (by
      intro allocated values h
      change (values.map model.image.toVal).all (fun v => Val.hasTy v model.type.toRaw allocated) = true
      apply List.all_eq_true.mpr
      intro v hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact model.member allocated a (h a ha))

def pair (left : ValueModel α) (right : ValueModel β) : ValueModel (α × β) :=
  ofImage (Image.tuple2 left.image right.image) (.prod left.type.toRaw right.type.toRaw)
    (fun allocated value => left.needs allocated value.1 ∧ right.needs allocated value.2)
    (by
      intro allocated value h
      change (Val.hasTy (left.image.toVal value.1) left.type.toRaw allocated &&
        Val.hasTy (right.image.toVal value.2) right.type.toRaw allocated) = true
      rw [left.member allocated value.1 h.1, right.member allocated value.2 h.2]
      rfl)

end ValueModel
end Effect4.Program
