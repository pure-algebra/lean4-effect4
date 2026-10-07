import Effect4.Program.FoldOf
import Effect4.Program.Fold
import Effect4.Program.Admission
import Effect4.Program.NativeAtom
import Effect4.Program.Typed
import Effect4.Schema.Bridge
import Effect4.Schema.Codec

/-!
# Type traversals and fold connections

`fold_of` connects the listed structural definitions to their generated type algebra.
Accumulator-shaped definitions carry their extra arguments in the algebra's result.
Schema writing uses `Bridge.schemaAlg` directly.
The JSON boundary uses one `Codec.wireAlgebra`; layout, support, encoding and decoding project its result.
Their connectors retain the existing outward names.
The traversal census owns the classification of each declaration.
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
fold_of Effect4.Program.payloadFieldTy
fold_of Effect4.Program.excludedAt
fold_of Effect4.Program.NativeAtom.projectProduct
fold_of Effect4.Program.Tuple.project
fold_of Effect4.Program.Val.hasTy

end Effect4.Program

namespace Effect4.Schema.Bridge.schema

/-- The Schema writer already uses this algebra through the generated type fold. -/
abbrev alg := Effect4.Schema.Bridge.schemaAlg

/-- Direct fold connection for Schema writing; serves the two Schema embedding claims. -/
theorem eq_cata (t : Effect4.Program.Ty) :
    Effect4.Schema.Bridge.schema t = Effect4.Program.cata_ty alg t := rfl

end Effect4.Schema.Bridge.schema

namespace Effect4.Schema.Codec
open Effect4.Program

/-- The JSON boundary uses one generated type fold; each outward operation is its projection. -/
theorem wire.eq_cata (t : Ty) : wire t = cata_ty wireAlgebra t := rfl

theorem layout.eq_cata (t : Ty) : layout t = (cata_ty wireAlgebra t).layout := rfl

theorem isSupported.eq_cata (t : Ty) : isSupported t = (cata_ty wireAlgebra t).supported := rfl

theorem encodeRaw.eq_cata (t : Ty) (v : Effect4.Machine.Val) :
    encodeRaw t v = (cata_ty wireAlgebra t).encode v := rfl

theorem decodeRaw.eq_cata (t : Ty) (j : Effect4.Json) :
    decodeRaw t j = (cata_ty wireAlgebra t).decode j := rfl

end Effect4.Schema.Codec
