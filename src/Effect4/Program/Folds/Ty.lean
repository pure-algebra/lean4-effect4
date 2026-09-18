import Effect4.Program.FoldOf
import Effect4.Program.Fold
import Effect4.Program.Admission
import Effect4.Program.NativeAtom
import Effect4.Schema.Bridge
import Effect4.Schema.Codec

/-!
# The hand traversals of `Ty` as folds

Every structural definition over `Ty` the census lists (`docs/core/traversal-census.md` §3.2)
that recurses only on immediate children with nothing accumulated, read as a `TyAlgebra` with
its connector `g.eq_cata : ∀ t, g t = cata_ty g.alg t`. The ones that thread a second value
(`Val.hasTy`, `Codec.encodeRaw`, `Codec.decodeRaw`, `instReprTy.repr`, `Ty.Le`, `findInt`) are the
fold-returning-a-function shape, not yet handled by `fold_of`.
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
fold_of Effect4.Schema.Bridge.schema
fold_of Effect4.Schema.Codec.layout
fold_of Effect4.Schema.Codec.isSupported

end Effect4.Program
