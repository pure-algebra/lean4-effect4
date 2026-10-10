import Tools.Session
import Tools.View.Program
import Effect4.Api.RefusalsDerived

/-! Finite controls placed in PLAN.md. These test commit 41ec1e0c.
The proposed module-layer field is absent at this base.
The signature control tests its required premise, not an admitted runtime counterexample. -/
namespace CxRefusalReview
open Effect4 Effect4.Program Effect4.Store

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def unitP : NativeEff := .succeed (.lit .unit)
def leaf : LayerTerm NativeOp := .succeed key (.nat 7)
def around (l : LayerTerm NativeOp) : NativeEff := .provideLayer l false unitP

def inside : NativeEff := around (.merge (.ref [0]) leaf)
def forward : NativeEff := around (.merge (.ref [0, 1]) leaf)
def toReference : NativeEff := around (.merge leaf (.merge (.ref [0, 0]) (.ref [0, 1, 0])))
def missing : NativeEff := around (.merge leaf (.ref [0, 0, 5]))
def crossScope : NativeEff :=
  .defs [{ name := "d", request := .unit, answer := .nat }]
    (.cons (.provideLayer leaf false (.service key)) .nil)
    (.provideLayer (.ref [0, 0, 0]) false (.service key))
def sameScope : NativeEff :=
  .defs [{ name := "d", request := .unit, answer := .nat }]
    (.cons (.provideLayer leaf false (.provideLayer (.ref [0, 0, 0]) false (.service key))) .nil)
    (.succeed (.lit (.nat 1)))

#guard Api.explain inside = some ⟨[0, 0], .referenceIllFormed [0] .encloses⟩
#guard Api.explain forward = some ⟨[0, 0], .referenceIllFormed [0, 1] .notBefore⟩
#guard Api.explain toReference = some ⟨[0, 1, 1], .referenceIllFormed [0, 1, 0] .toReference⟩
#guard Api.explain missing = some ⟨[0, 1], .referenceIllFormed [0, 0, 5] .noLayer⟩
#guard Api.explain crossScope = some ⟨[1, 0], .referenceIllFormed [0, 0, 0] .otherScope⟩
#guard Api.explain sameScope = none
#guard Api.wellTyped sameScope

-- Distinguish the first fault from a later fault, then skip an earlier valid reference.
def twoFaults : NativeEff := around (.merge (.ref [9]) (.ref [0]))
def skipValid : NativeEff := around (.merge leaf (.merge (.ref [0, 0]) (.ref [9])))
#guard twoFaults.refSites [] = [([0, 0], [9]), ([0, 1], [0])]
#guard twoFaults.refFault [0, 1] [0] = some .encloses
#guard twoFaults.firstRefFault = some ([0, 0], [9], .notBefore)
#guard skipValid.refSites [] = [([0, 1, 0], [0, 0]), ([0, 1, 1], [9])]
#guard skipValid.firstRefFault = some ([0, 1, 1], [9], .notBefore)

-- Child 2 has ordinary meaning when the root is not a definition block.
def handlerBackward : NativeEff :=
  .matchCause (around leaf) unitP (around (.ref [0, 0]))
def handlerForward : NativeEff :=
  .matchCause (around (.ref [2, 0])) unitP (around leaf)
#guard handlerBackward.layerRefsWF
#guard Api.explain handlerBackward = none
#guard !handlerForward.layerRefsWF
#guard Api.explain handlerForward = some ⟨[0, 0], .referenceIllFormed [2, 0] .notBefore⟩

-- The generated carrier retains distinctions that the present summary drops.
def r1 : TypeRefusal := ⟨[0, 1], .referenceIllFormed [0, 0, 5] .noLayer⟩
def r2 : TypeRefusal := ⟨[0, 1], .referenceIllFormed [0, 0, 5] .otherScope⟩
#guard Canonical.toVal r1 != Canonical.toVal r2
#guard Tools.Query.refusalJson r1 == Tools.Query.refusalJson r2
#guard Tools.Session.printJson r1 != Tools.Session.printJson r2
example : Canonical.ofVal (Canonical.toVal r1) = some r1 := Canonical.ofVal_toVal r1

-- An actual refusal reaches the tool summary without its target or specific fault.
#guard match Api.explain missing with
  | none => false
  | some r => (Tools.Query.refusalJson r).compress ==
      "{\"path\":[0,1],\"reason\":\"referenceIllFormed\"}"

-- A parameter-reading layer checks in the caller but not at module scope.
def param : ParamDecl := { name := "body", request := .unit, answer := .nat }
def parameterLayer : LayerTerm NativeOp := .effect key (.perform (.param 0) (.lit .unit))
def closedLayer : LayerTerm NativeOp := .effect key (.succeed (.lit (.nat 7)))
#guard !(Checker.checkLayer (nativeSignature []) [2, 0] parameterLayer).isOk
#guard (Checker.checkLayer ((nativeSignature []).withParams [param]) [2, 0] parameterLayer).isOk
#guard (Checker.checkLayer (nativeSignature []) [2, 0] closedLayer).isOk
#guard Checker.checkLayer (nativeSignature []) [2, 0] closedLayer ==
  Checker.checkLayer ((nativeSignature []).withParams [param]) [2, 0] closedLayer

-- Existing source-view boundary: the session still uses the structural refusal.
#guard (EditSession.open {} { program := missing }).view.refusals.any fun r =>
  r.path == [0, 1] && r.reason.head == "layerReference"
#guard !(Tools.View.Program.sessionPage
  (EditSession.open {} { program := missing }) none "" "" "" "").lines.any fun l =>
    l.state == .refused

#eval (Tools.Query.refusalJson r1).compress
#eval (Tools.Session.printJson r1).compress
#eval ((Tools.Session.answer {} { op := "open", programJson := some (Tools.Session.printJson missing) }).2.result).compress
end CxRefusalReview
