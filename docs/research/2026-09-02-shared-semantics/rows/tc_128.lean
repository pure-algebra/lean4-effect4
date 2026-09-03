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
abbrev row : Signature := (atom 0 ⊕ₛ (atom 1 ⊕ₛ (atom 2 ⊕ₛ (atom 3 ⊕ₛ (atom 4 ⊕ₛ (atom 5 ⊕ₛ (atom 6 ⊕ₛ (atom 7 ⊕ₛ (atom 8 ⊕ₛ (atom 9 ⊕ₛ (atom 10 ⊕ₛ (atom 11 ⊕ₛ (atom 12 ⊕ₛ (atom 13 ⊕ₛ (atom 14 ⊕ₛ (atom 15 ⊕ₛ (atom 16 ⊕ₛ (atom 17 ⊕ₛ (atom 18 ⊕ₛ (atom 19 ⊕ₛ (atom 20 ⊕ₛ (atom 21 ⊕ₛ (atom 22 ⊕ₛ (atom 23 ⊕ₛ (atom 24 ⊕ₛ (atom 25 ⊕ₛ (atom 26 ⊕ₛ (atom 27 ⊕ₛ (atom 28 ⊕ₛ (atom 29 ⊕ₛ (atom 30 ⊕ₛ (atom 31 ⊕ₛ (atom 32 ⊕ₛ (atom 33 ⊕ₛ (atom 34 ⊕ₛ (atom 35 ⊕ₛ (atom 36 ⊕ₛ (atom 37 ⊕ₛ (atom 38 ⊕ₛ (atom 39 ⊕ₛ (atom 40 ⊕ₛ (atom 41 ⊕ₛ (atom 42 ⊕ₛ (atom 43 ⊕ₛ (atom 44 ⊕ₛ (atom 45 ⊕ₛ (atom 46 ⊕ₛ (atom 47 ⊕ₛ (atom 48 ⊕ₛ (atom 49 ⊕ₛ (atom 50 ⊕ₛ (atom 51 ⊕ₛ (atom 52 ⊕ₛ (atom 53 ⊕ₛ (atom 54 ⊕ₛ (atom 55 ⊕ₛ (atom 56 ⊕ₛ (atom 57 ⊕ₛ (atom 58 ⊕ₛ (atom 59 ⊕ₛ (atom 60 ⊕ₛ (atom 61 ⊕ₛ (atom 62 ⊕ₛ (atom 63 ⊕ₛ (atom 64 ⊕ₛ (atom 65 ⊕ₛ (atom 66 ⊕ₛ (atom 67 ⊕ₛ (atom 68 ⊕ₛ (atom 69 ⊕ₛ (atom 70 ⊕ₛ (atom 71 ⊕ₛ (atom 72 ⊕ₛ (atom 73 ⊕ₛ (atom 74 ⊕ₛ (atom 75 ⊕ₛ (atom 76 ⊕ₛ (atom 77 ⊕ₛ (atom 78 ⊕ₛ (atom 79 ⊕ₛ (atom 80 ⊕ₛ (atom 81 ⊕ₛ (atom 82 ⊕ₛ (atom 83 ⊕ₛ (atom 84 ⊕ₛ (atom 85 ⊕ₛ (atom 86 ⊕ₛ (atom 87 ⊕ₛ (atom 88 ⊕ₛ (atom 89 ⊕ₛ (atom 90 ⊕ₛ (atom 91 ⊕ₛ (atom 92 ⊕ₛ (atom 93 ⊕ₛ (atom 94 ⊕ₛ (atom 95 ⊕ₛ (atom 96 ⊕ₛ (atom 97 ⊕ₛ (atom 98 ⊕ₛ (atom 99 ⊕ₛ (atom 100 ⊕ₛ (atom 101 ⊕ₛ (atom 102 ⊕ₛ (atom 103 ⊕ₛ (atom 104 ⊕ₛ (atom 105 ⊕ₛ (atom 106 ⊕ₛ (atom 107 ⊕ₛ (atom 108 ⊕ₛ (atom 109 ⊕ₛ (atom 110 ⊕ₛ (atom 111 ⊕ₛ (atom 112 ⊕ₛ (atom 113 ⊕ₛ (atom 114 ⊕ₛ (atom 115 ⊕ₛ (atom 116 ⊕ₛ (atom 117 ⊕ₛ (atom 118 ⊕ₛ (atom 119 ⊕ₛ (atom 120 ⊕ₛ (atom 121 ⊕ₛ (atom 122 ⊕ₛ (atom 123 ⊕ₛ (atom 124 ⊕ₛ (atom 125 ⊕ₛ (atom 126 ⊕ₛ atom 127)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def witness0 : Has (atom 0) row := inferInstance
def witness64 : Has (atom 64) row := inferInstance
def witness127 : Has (atom 127) row := inferInstance
