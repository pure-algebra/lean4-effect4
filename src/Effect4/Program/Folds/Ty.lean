import Effect4.Program.FoldOf
import Effect4.Program.Fold
import Effect4.Program.Admission
import Effect4.Program.NativeAtom
import Effect4.Program.Typed
import Effect4.Schema.Bridge
import Effect4.Schema.Codec

/-!
# The hand traversals of `Ty` as folds

Every structural definition over `Ty` the census lists (`docs/core/traversal-census.md` §3.2),
read as a `TyAlgebra` with its connector `g.eq_cata : ∀ …, g … t … = cata_ty g.alg t …`. The
accumulator-shaped ones carry their other arguments in the carrier: `findInt.alg` at
`Path → Option Path`, `Val.hasTy.alg` at `Val → List String → Bool`, `Codec.encodeRaw.alg` at
`Val → Option Json` and `Codec.decodeRaw.alg` at `Json → Option Val` — the two-discriminant
matches (`| .unit, .unit => …`) read as the case split on the type with the value's split
inside. Not here: `instReprTy.repr` and `Ty.Le` (a `Prop`-valued relation on two types).
-/

namespace Effect4.Program

fold_of Effect4.Program.Ty.renderRaw
fold_of Effect4.Program.Ty.members
fold_of Effect4.Program.Ty.key
fold_of Effect4.Program.Ty.isNever
fold_of Effect4.Program.Ty.isMember
fold_of Effect4.Program.Ty.normalize
fold_of Effect4.Program.isTagTy
fold_of Effect4.Program.rawSupportedErrTy
fold_of Effect4.Program.NativeAtom.projectProduct
fold_of Effect4.Program.findInt
fold_of Effect4.Program.Val.hasTy
fold_of Effect4.Schema.Bridge.schema
fold_of Effect4.Schema.Codec.layout
fold_of Effect4.Schema.Codec.isSupported
fold_of Effect4.Schema.Codec.encodeRaw
fold_of Effect4.Schema.Codec.decodeRaw

end Effect4.Program
