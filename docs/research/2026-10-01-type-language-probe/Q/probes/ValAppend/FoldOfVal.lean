import Effect4.Program.FoldOf
import ProbeQV.Fold

/-! Seat Q, the `Val` append: the tree's `fold_of` registrations over `Store.Val`
(`src/Effect4/Laws/Store/Folds/Val.lean:26-38`), run on the copy with the two frames, for the
definitions the copy carries (`refs`, `malformedRef`, `acceptsAt`, `printIn` and
`Config.Val.ofStore` live outside `Val.lean`). A registration that compiles derives its algebra
and connectors with no hand line. -/

namespace ProbeQV

fold_of ProbeQV.Val.render
fold_of ProbeQV.Val.encode
fold_of ProbeQV.Val.tag
fold_of ProbeQV.Val.handles
fold_of ProbeQV.Val.beq
fold_of ProbeQV.Val.WF
fold_of ProbeQV.Val.wf
fold_of ProbeQV.Val.payload

end ProbeQV

#print axioms ProbeQV.Val.encode.hom
#print axioms ProbeQV.Val.WF.hom
#print axioms ProbeQV.Val.payload.hom
#print axioms ProbeQV.Val.beq.hom
#check @ProbeQV.Val.encode.alg
