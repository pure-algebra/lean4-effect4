import ProbeU.Generic
import Effect4.Program.Eff
import Effect4.Program.NativeAtom

/-!
# Probe U, question 2, family (b2): the union-spine folds are one generic fold at four atoms

`Ty.members`, `isTagTy`, `rawSupportedErrTy` and `NativeAtom.projectProduct` recurse through
`union` only: `never` is the bottom, `union` the join, and every other node is an atom read
whole by a one-level classifier. That is the free join-semilattice reading of a type, the
structure `normalize` and the row algebra already rest on (`Ty.normalizeRow`, `Effect4.Row`).
One generic paramorphism (`spineAlg`: the node paired in, so an atom sees itself) with four
atom classifiers reproduces the four hand traversals; each agreement is the generated
uniqueness theorem with definitional fields.

The catch-all of `spineLayer` ("every other constructor is an atom") is the semantics of the
union spine, not a default: a constructor the wave appends (`record`, `tuple`, `app`, …) is an
atom of the spine, as it must be. The classifiers keep row 56's rule — positive arms listed,
an explicit negative last — so an appended constructor is a member, not a tag, not a supported
error payload and not a product until its own arm says otherwise.
-/

set_option autoImplicit false

open Effect4 Effect4.Program ProbeU

namespace ProbeU.Spine

/-- One layer of the union spine. -/
def spineLayer {R : Type} (bot : R) (join : R → R → R) (atom : Ty → R) :
    TyCtor → TyLeaf → List (Ty × R) → Ty × R
  | .never, l, kids => (tyBuild .never l (kids.map (·.1)), bot)
  | .union, l, [a, b] => (tyBuild .union l [a.1, b.1], join a.2 b.2)
  | c, l, kids => let n := tyBuild c l (kids.map (·.1)); (n, atom n)

def spineAlg {R : Type} (bot : R) (join : R → R → R) (atom : Ty → R) : TyAlgebra (fun _ => Ty × R) :=
  TyAlgebra.ofLayer (spineLayer bot join atom)

/-- A union-spine fold: the second component of the paired fold. -/
def spineFold {R : Type} (bot : R) (join : R → R → R) (atom : Ty → R) (t : Ty) : R :=
  (cata_ty (spineAlg bot join atom) t).2

/-- The members: every atom is its own member. -/
theorem members_eq (t : Ty) : Ty.members t = spineFold [] (· ++ ·) (fun a => [a]) t :=
  congrArg Prod.snd (hom_eq_cata_ty (alg := spineAlg [] (· ++ ·) (fun a => [a]))
    { f_ty := fun s => (s, Ty.members s)
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t)

/-- A tag atom: a string or a string literal. -/
def tagAtom : Ty → Bool
  | .string | .lit _ => true
  | _ => false

theorem isTagTy_eq (t : Ty) : isTagTy t = spineFold false (· && ·) tagAtom t :=
  congrArg Prod.snd (hom_eq_cata_ty (alg := spineAlg false (· && ·) tagAtom)
    { f_ty := fun s => (s, isTagTy s)
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t)

/-- A supported error atom (DI-15, DI-62): a natural, a string, a literal, or a pair of tags. -/
def errAtom : Ty → Bool
  | .nat | .string | .lit _ => true
  | .prod a b => isTagTy a && isTagTy b
  | _ => false

theorem rawSupportedErrTy_eq (t : Ty) : rawSupportedErrTy t = spineFold true (· && ·) errAtom t :=
  congrArg Prod.snd (hom_eq_cata_ty (alg := spineAlg true (· && ·) errAtom)
    { f_ty := fun s => (s, rawSupportedErrTy s)
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t)

/-- A product atom: its selected column. -/
def projAtom (second : Bool) : Ty → Option Ty
  | .prod a b => some (if second then b else a)
  | _ => none

/-- Two projected columns joined (the canonical join), when both exist. -/
def projJoin (l r : Option Ty) : Option Ty := do
  let left ← l
  let right ← r
  some (Ty.join left right)

theorem projectProduct_eq (second : Bool) (t : Ty) :
    NativeAtom.projectProduct second t = spineFold (some Ty.never) projJoin (projAtom second) t :=
  congrArg Prod.snd (hom_eq_cata_ty (alg := spineAlg (some Ty.never) projJoin (projAtom second))
    { f_ty := fun s => (s, NativeAtom.projectProduct second s)
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t)

#guard Ty.members (.union .nat (.union .never (.lit "a"))) == [.nat, .lit "a"]
#guard spineFold [] (· ++ ·) (fun a => [a]) (.union .nat (.union .never (.lit "a"))) == [.nat, .lit "a"]

end ProbeU.Spine

#print axioms ProbeU.Spine.members_eq
#print axioms ProbeU.Spine.isTagTy_eq
#print axioms ProbeU.Spine.rawSupportedErrTy_eq
#print axioms ProbeU.Spine.projectProduct_eq
