from pathlib import Path
p=Path('/tmp/effect4-row-research-20260902')
pre='''import Effects.Morphism
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
'''
for n in [8,16,32,64,128,256]:
    row=f'atom {n-1}'
    for i in reversed(range(n-1)): row=f'(atom {i} ⊕ₛ {row})'
    for mode in ['tc','explicit']:
        text=pre+f'abbrev row : Signature := {row}\n'
        for j in [0,n//2,n-1]:
            if mode=='tc': text+=f'def witness{j} : Has (atom {j}) row := inferInstance\n'
            else:
                term='Signature.Hom.id _' if j==n-1 else 'Signature.Hom.inl'
                for i in range(j): term=f'({term}).comp Signature.Hom.inr'
                text+=f'def witness{j} : Signature.Hom (atom {j}) row := {term}\n'
        (p/f'{mode}_{n}.lean').write_text(text)
(p/'baseline.lean').write_text(pre)
(p/'universes.lean').write_text('''import Effects.Morphism
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
''')
