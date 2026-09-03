import Effects.Morphism
open Effects
set_option pp.universes true
#check Signature
#check Signature.sum
#check Signature.Hom
#check Program
#check @Signature.Hom.inl
universe u v
example (S : Signature.{u,0}) (T : Signature.{v,0}) : Signature.{max u v,0} := S ⊕ₛ T
example (S : Signature.{1,1}) (T : Signature.{2,1}) : Signature.{2,1} := S ⊕ₛ T
-- Expected rejection: no implicit answer-universe lift.
#check_failure fun (S : Signature.{0,0}) (T : Signature.{0,1}) => S ⊕ₛ T
