import CXControls
import Effect4.Author

/-! Finite CX3 boundary controls; placement precedes them in CX-PLAN.md. -/
set_option autoImplicit false
namespace Test.CX3DecisionReview
open Effect4 Effect4.Program Effect4.Machine
open Test.CXLayerContextReview (key u admittedRun)

def capParam : ParamDecl := { name := "p", request := .unit, answer := .nat }
def capDecl : DefDecl := { name := "capture", request := .unit, answer := .nat, params := [capParam] }
def capBody : NativeEff :=
  .provideLayer (.effect key (.perform (.param 0) u)) false (.service key)
def captured : NativeEff :=
  .defs [capDecl] (.cons capBody .nil)
    (.bind (.succeed (.lit (.nat 41)))
      (.invoke 0 u (.cons (.succeed (.var 0)) .nil)))
def rawCaptured : NativeEff :=
  .bind (.succeed (.lit (.nat 41)))
    (.provideLayer (.effect key (.succeed (.var 0))) false (.service key))

#guard (admitProgram captured).toOption.isSome
#guard Api.typeOf captured = some (EffTy.pure .nat)
#guard (admittedRun captured).map Api.Inspection.exit = some (some (.success (.nat 41)))
#guard (admitProgram rawCaptured).toOption.isNone

-- Declared bounds remain relevant after a parameter call, even for a narrower argument.
def listParam : ParamDecl := { name := "p", request := .unit, answer := .list .nat }
def refDecl : DefDecl :=
  { name := "allocate", request := .unit, answer := .refOf (.list .nat), params := [listParam] }
def refBody : NativeEff := .bind (.perform (.param 0) u) (.perform .refMake (.var 1))
def emptyList : NativeEff := .succeed (.app "nil" .nil)
def referenceCall : NativeEff :=
  .defs [refDecl] (.cons refBody .nil) (.invoke 0 u (.cons emptyList .nil))
def rawReferenceBody : NativeEff := .bind emptyList (.perform .refMake (.var 1))

#guard (admitProgram referenceCall).toOption.isSome
#guard Api.typeOf referenceCall = some (EffTy.pure (.refOf (.list .nat)))
#guard Checker.check ({} : SigApp).signature [.unit] [] rawReferenceBody =
  .ok (EffTy.pure (.refOf (.list .never)))
#guard !(Ty.sub (.refOf (.list .never)) (.refOf (.list .nat)))

/-- Existing checked value ascription restores this allocation's declared answer. -/
def ascribedReferenceBody : Option NativeEff :=
  (Authoring.elaborate
    (Authoring.succeed (Authoring.ascribe (.list .nat) (Authoring.app "nil" [])) : Authoring.Src NativeOp)).toOption.map
      (fun e => .bind e (.perform .refMake (.var 1)))

#guard ascribedReferenceBody.isSome
#guard ascribedReferenceBody.map (Checker.check ({} : SigApp).signature [.unit] []) =
  some (.ok (EffTy.pure (.refOf (.list .nat))))

end Test.CX3DecisionReview
