import ProbeU.FacesTable

/-!
# Probe U, question 4 — the table's fold on the LCNF route

`renderTable` is `cata_ty (tsAlg tyFaces)`: the generic fold over the generated table. The tree's
LCNF translator (`src/OCaml5/Tools/LcnfGen.lean`) refuses `TyAlgebra R` itself ("unsupported
parameter R": a type-family parameter has no OCaml image; coherence principle §6.1 records the
same refusal for `EffAlgebra Op R`), so a fold defined through `cata_ty` does not lower as it
stands (`U/logs/lcnf-lowering.log`, first run). `cataS` is `cata_ty` with `@[specialize]` on the
algebra, the one-attribute change the generator would make: at a call whose algebra is a closed
value (a table read by a generic interpreter) the compiler specializes the fold to the table,
and no `TyAlgebra` value reaches the translator (second run).
-/

namespace ProbeU

open Effect4.Program

def renderTable (t : Ty) : String := cata_ty (tsAlg tyFaces) t

/-- `cata_ty` with its algebra specialized (the generated fold with one attribute added). -/
@[specialize alg]
def cataS {R : TyFam → Type} (alg : TyAlgebra R) (node : Ty) : R .ty :=
  match node with
  | .never => alg.ty_never
  | .unit => alg.ty_unit
  | .nat => alg.ty_nat
  | .int => alg.ty_int
  | .string => alg.ty_string
  | .bool => alg.ty_bool
  | .handle a0 => alg.ty_handle a0
  | .option a0 => alg.ty_option (cataS alg a0)
  | .list a0 => alg.ty_list (cataS alg a0)
  | .prod a0 a1 => alg.ty_prod (cataS alg a0) (cataS alg a1)
  | .except a0 a1 => alg.ty_except (cataS alg a0) (cataS alg a1)
  | .exitOf a0 a1 => alg.ty_exitOf (cataS alg a0) (cataS alg a1)
  | .causeOf a0 => alg.ty_causeOf (cataS alg a0)
  | .fiberOf a0 a1 => alg.ty_fiberOf (cataS alg a0) (cataS alg a1)
  | .union a0 a1 => alg.ty_union (cataS alg a0) (cataS alg a1)
  | .lit a0 => alg.ty_lit a0
  | .refOf a0 => alg.ty_refOf (cataS alg a0)
  | .deferredOf a0 a1 => alg.ty_deferredOf (cataS alg a0) (cataS alg a1)
  | .var a0 => alg.ty_var a0
  | .unknown => alg.ty_unknown
termination_by structural node

def renderTableS (t : Ty) : String := cataS (tsAlg tyFaces) t

/-- The specialized fold is the generated one (proved: the same equations). -/
theorem cataS_eq {R : TyFam → Type} (alg : TyAlgebra R) (t : Ty) : cataS alg t = cata_ty alg t :=
  hom_eq_cata_ty (alg := alg)
    { f_ty := cataS alg
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

/-- The layer algebra and the TypeScript interpreter, inlined (what `@[inline]` on the emitted
`ofLayer` and on a face's algebra would give). -/
@[inline] def ofLayerI {X : Type} (layer : TyCtor → TyLeaf → List X → X) : TyAlgebra (fun _ => X) where
  ty_never := layer .never .none []
  ty_unit := layer .unit .none []
  ty_nat := layer .nat .none []
  ty_int := layer .int .none []
  ty_string := layer .string .none []
  ty_bool := layer .bool .none []
  ty_handle a0 := layer .handle (.str a0) []
  ty_option a0 := layer .option .none [a0]
  ty_list a0 := layer .list .none [a0]
  ty_prod a0 a1 := layer .prod .none [a0, a1]
  ty_except a0 a1 := layer .except .none [a0, a1]
  ty_exitOf a0 a1 := layer .exitOf .none [a0, a1]
  ty_causeOf a0 := layer .causeOf .none [a0]
  ty_fiberOf a0 a1 := layer .fiberOf .none [a0, a1]
  ty_union a0 a1 := layer .union .none [a0, a1]
  ty_lit a0 := layer .lit (.str a0) []
  ty_refOf a0 := layer .refOf .none [a0]
  ty_deferredOf a0 a1 := layer .deferredOf .none [a0, a1]
  ty_var a0 := layer .var (.nat a0) []
  ty_unknown := layer .unknown .none []

@[inline] def tsAlgI (tbl : TyTable FaceRow) : TyAlgebra (fun _ => String) :=
  ofLayerI fun c l kids => (tbl.get c).ts.render (tsLeaf l) kids

def renderTableI (t : Ty) : String := cataS (tsAlgI tyFaces) t

end ProbeU

#print axioms ProbeU.cataS_eq
