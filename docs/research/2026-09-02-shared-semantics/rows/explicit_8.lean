import Effects.Morphism
set_option warn.classDefReducibility false
open Effects
universe uS uR uL uA
class Has (S : Signature.{uS,uA}) (R : Signature.{uR,uA}) where
  hom : Signature.Hom S R
instance (priority := 1000) : Has S S := ⟨Signature.Hom.id S⟩
instance (priority := 900) : Has S (S ⊕ₛ T) := ⟨Signature.Hom.inl⟩
instance (priority := 800) [h : Has S R] : Has S (L ⊕ₛ R) :=
  ⟨h.hom.comp Signature.Hom.inr⟩
inductive Tag (n : Nat) where | tag
def atom (n : Nat) : Signature := ⟨Tag n, fun _ => Unit⟩
abbrev row : Signature := (atom 0 ⊕ₛ (atom 1 ⊕ₛ (atom 2 ⊕ₛ (atom 3 ⊕ₛ (atom 4 ⊕ₛ (atom 5 ⊕ₛ (atom 6 ⊕ₛ atom 7)))))))
def witness0 : Signature.Hom (atom 0) row := Signature.Hom.inl
def witness4 : Signature.Hom (atom 4) row := ((((Signature.Hom.inl).comp Signature.Hom.inr).comp Signature.Hom.inr).comp Signature.Hom.inr).comp Signature.Hom.inr
def witness7 : Signature.Hom (atom 7) row := (((((((Signature.Hom.id _).comp Signature.Hom.inr).comp Signature.Hom.inr).comp Signature.Hom.inr).comp Signature.Hom.inr).comp Signature.Hom.inr).comp Signature.Hom.inr).comp Signature.Hom.inr
