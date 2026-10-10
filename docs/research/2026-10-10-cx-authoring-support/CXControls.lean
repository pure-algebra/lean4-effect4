import LayerContextControls
import Effect4.Program.Typing.Parts

/-! Finite scope and memo controls. Placement: CX-PLAN.md.
No claim about Effect runtime execution follows from these evaluations. -/
set_option autoImplicit false
namespace Test.CXDecisionReview
open Effect4 Effect4.Program Effect4.Machine
open Test.CXLayerContextReview (key u slot arg admittedRun)

def nestedDecl : DefDecl :=
  { name := "nested", request := .bool, answer := .nat, params := [slot] }

def nestedProgram (fresh localMemo : Bool) : NativeEff :=
  let layer : LayerTerm NativeOp := .effect key (.perform (.param 0) u)
  .defs [nestedDecl]
    (.cons
      (.provideLayer (if fresh then .fresh layer else layer) localMemo
        (.select (.var 0) .bool
          (.invoke 0 (.lit (.bool false)) (arg 2))
          (.service key)))
      .nil)
    (.invoke 0 (.lit (.bool true)) (arg 1))

#guard (nestedProgram false false).refSites [] = []
#guard (nestedProgram false false).layerRefsWF
#guard (admitProgram (nestedProgram false false)).toOption.isSome
#guard Api.typeOf (nestedProgram false false) = some (EffTy.pure .nat)
#guard (admittedRun (nestedProgram false false)).map Api.Inspection.exit = some (some (.success (.nat 1)))
#guard (admittedRun (nestedProgram true false)).map Api.Inspection.exit = some (some (.success (.nat 2)))
#guard (admittedRun (nestedProgram false true)).map Api.Inspection.exit = some (some (.success (.nat 2)))

-- Different definition bodies can have identical parameter declarations.
-- Such equality supplies the existing typing hop, but does not enforce lexical visibility.
#guard scopeParams (Test.CXLayerContextReview.makeProgram false) [0, 0, 0] =
  scopeParams (Test.CXLayerContextReview.makeProgram false) [0, 1, 0, 0]
#guard (Test.CXLayerContextReview.makeProgram false).layerRefsWF

/-- A probe-only owner reader, derived from an existing part and its remaining path. -/
def ownerAt (root : NativeEff) (path : List Nat) : Option (List Nat) :=
  (root.partAt ({} : SigApp).signature [] path).map fun (_, rest) =>
    path.take (path.length - rest.length)

/-- Candidate option (a), for finite policy checks only. -/
def localRefs (root : NativeEff) : Bool :=
  root.layerRefsWF && (root.refSites []).all fun (site, target) =>
    match ownerAt root site, ownerAt root target with
    | some a, some b => decide (a = b)
    | _, _ => false

def localReference : NativeEff :=
  .defs [Test.CXLayerContextReview.decl "local"]
    (.cons
      (.bind
        (.provideLayer (.effect key (.perform (.param 0) u)) false
          Test.CXLayerContextReview.unitEff)
        (.provideLayer (.ref [0, 0, 0, 0]) false (.service key)))
      .nil)
    (.invoke 0 u (arg 1))

#guard !(localRefs (Test.CXLayerContextReview.failureProgram false 2))
#guard !(localRefs Test.CXLayerContextReview.closedCrossScope)
#guard !(localRefs (Test.CXLayerContextReview.makeProgram false))
#guard localRefs localReference
#guard (admitProgram localReference).toOption.isSome
#guard (admittedRun localReference).map Api.Inspection.exit = some (some (.success (.nat 1)))
#guard localRefs (nestedProgram false false)

/-- Candidate option (e): lexical identity or no incoming parameter reads after expansion. -/
def closedRefs (root : NativeEff) : Bool :=
  root.layerRefsWF && (root.refSites []).all fun (site, target) =>
    match ownerAt root site, ownerAt root target with
    | some a, some b => decide (a = b) ||
        (Test.CXLayerContextReview.usedParams (LayerTerm.expandIn root (.ref target))).isEmpty
    | _, _ => false

-- The referenced closed target calls a definition that uses its own newly supplied parameter.
def closedInvoker : NativeEff :=
  .defs [Test.CXLayerContextReview.errDecl "target" .never,
      Test.CXLayerContextReview.errDecl "callee" .never]
    (.cons
      (.provideLayer
        (.effectDiscard (.invoke 1 u (.cons Test.CXLayerContextReview.unitEff .nil))) false
        Test.CXLayerContextReview.unitEff)
      (.cons (.perform (.param 0) u) .nil))
    (.provideLayer (.ref [0, 0, 0]) false Test.CXLayerContextReview.unitEff)

#guard !(closedRefs (Test.CXLayerContextReview.failureProgram false 2))
#guard !(closedRefs (Test.CXLayerContextReview.makeProgram false))
#guard closedRefs Test.CXLayerContextReview.closedCrossScope
#guard closedRefs localReference
#guard closedRefs (nestedProgram false false)
#guard closedRefs closedInvoker
#guard !(localRefs closedInvoker)
#guard (admitProgram closedInvoker).toOption.isSome
#guard (admittedRun closedInvoker).map Api.Inspection.exit = some (some (.success .unit))

end Test.CXDecisionReview
