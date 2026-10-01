import ProbeU.TyFoldExtras

/-!
# Probe U — the generic fold families of `Ty`, as the patched generator emits them

Everything a worked instance reads — the one-level view (`TyCtor`, `tyCtor`, `TyLeaf`,
`tyLeaf`, `tyKids`, `tyBuild` and `tyBuild_view`), the per-constructor table type `TyTable`,
the layer algebra `TyAlgebra.ofLayer` with `cata_ofLayer_view` and the per-layer invariant
`cata_ofLayer_inv`, the head fold and the paired fold with their connectors
(`foldMap_head_eq_cata`, `foldMap_eq_cata`), fusion (`TyAlgebra.Commutes`, `cata_fusion_ty`) and
the banana split (`TyAlgebra.prod`, `cata_prod_ty`) — is the module
`U/generated/ProbeU/TyFoldExtras.lean`, written by the seat's patched copy of
`tools/Effect4Gen/Fold.lean` (`U/patches/Fold.lean`, `--extras`) from the declaration of `Ty`
alone (`U/logs/gen-extras.log`). This file adds the two generic laws the emitted file does not
carry. The first hand-written draft of the emitted shapes is kept as history in
`U/scratch/Generic.handwritten.lean` (not committed).
-/

set_option autoImplicit false

namespace ProbeU

open Effect4.Program

universe u

/-- The paired fold's first component is the node: the paramorphism reads its argument back. -/
theorem paraAlg_fst {M : Type u} (unit : M) (op : M → M → M) (f : Ty → M) (t : Ty) :
    (cata_ty (TyAlgebra.paraAlg op f) t).1 = t := by
  rw [← foldMap_eq_cata unit op f t]

/-- And its second component is `foldMap_ty`. -/
theorem paraAlg_snd {M : Type u} (unit : M) (op : M → M → M) (f : Ty → M) (t : Ty) :
    (cata_ty (TyAlgebra.paraAlg op f) t).2 = foldMap_ty unit op t f := by
  rw [← foldMap_eq_cata unit op f t]

end ProbeU

#print axioms ProbeU.paraAlg_fst
#print axioms ProbeU.paraAlg_snd
