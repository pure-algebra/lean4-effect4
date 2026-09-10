import Effect4.Laws.Program.Typing.Check
import Effect4.Program.Native

namespace Test.Program.TypingCheckContract
open Effect4.Program Conform.Effect4.Typing

def accepted : Eff NativeOp := .succeed (.lit (.nat 7))
def refused : Eff NativeOp := .fail (.lit (.bool true))

#guard (checkTyping nativeSignature [] accepted).toOption.map (·.val) =
  some (EffTy.pure .nat)
#guard (checkTyping nativeSignature [] refused).toOption.isNone
#guard (assessTyping nativeSignature [] accepted).remaining =
  [.valueModel, .targetRepresentation, .executionRelation, .hostBehavior]

/-- The returned proof is indexed by this exact input, rather than a reported theorem name. -/
theorem returned_judgment (sig : Signature Op) (env : TyEnv) (program : Eff Op)
    (result : { t : EffTy // HasTy sig env program t }) : HasTy sig env program result.val :=
  result.property

#print axioms checkTyping
#print axioms checkTyping_refuses_iff
#print axioms checkTyping_spec
#print axioms returned_judgment
end Test.Program.TypingCheckContract
