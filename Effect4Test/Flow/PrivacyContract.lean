import Effect4.Flow.Checked

/-!
# Checked Flow constructor privacy

`CheckedFlow` is proof carrying, but possession of the public `raw` and `wf`
projections must not expose an unchecked construction path.  Admission is the
only public constructor boundary.
-/

namespace Effect4Test.Flow.PrivacyContract

open Effect4

/-!
E4-FLOW-CE-015: the generated-looking constructor name must remain
unresolvable from an importing module.  If `private mk ::` is changed to
`mk ::`, this compile-negative stops producing the required error and the
default test root fails.
-/

/--
error: Unknown constant
-/
#guard_msgs(error, substring := true) in
#check (@CheckedFlow.mk)

section RecordLiteral

universe uTy uOp

variable {Ty : Type uTy} {alphabet : FlowAlphabet.{uTy, uOp} Ty}
variable (raw : RawFlow Ty) (wf : FlowWF alphabet raw)

/--
error: invalid {...} notation, constructor for `CheckedFlow` is marked as private
-/
#guard_msgs(error, substring := true) in
#check ({ raw := raw, wf := wf } : CheckedFlow alphabet)

end RecordLiteral

end Effect4Test.Flow.PrivacyContract
