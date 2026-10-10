import Effect4.Laws.Program.Typed.Scope
import Effect4.Laws.Program.Typed.Adequacy
import Effect4.Api

/-!
Memo-table migration control at f00008ee.
Concept: store-typing; property: memo cell columns; consumers: memoBuild_world,
memoGet_implements, memoComplete_implements, hence denote-typed through layer memoization.
Reach: one admitted parameterized definition and its effectDiscard layer.
Limits: no runtime defect or full CX1b preservation is claimed.
Unlock: include the stored memo-cell condition in the context migration (R4, M6).
-/
set_option autoImplicit false
namespace Test.CX1aMemoReview
open Effect4 Effect4.Program Effect4.Program.Typed Effect4.Machine

def unitProgram : NativeEff := .succeed (.lit .unit)
def parameterRun : NativeEff := .perform (.param 0) (.lit .unit)
def slot : ParamDecl := { name := "p", request := .unit, answer := .unit }
def decl : DefDecl :=
  { name := "build", request := .unit, answer := .unit, params := [slot] }
def layer : LayerTerm NativeOp := .effectDiscard parameterRun
def body : NativeEff := .provideLayer layer false unitProgram
def program : NativeEff := .defs [decl] (.cons body .nil)
  (.invoke 0 (.lit .unit) (.cons unitProgram .nil))
def source : ProgramSource := { program }
def layerPath : List Nat := [0, 0, 0]

#guard Api.typeOf program == some (EffTy.pure .unit)
#guard Node.at_ (.eff program) layerPath == some (.layer layer)
#guard scopeParams program layerPath == [slot]
#guard (Checker.checkLayer source.signature layerPath
  (LayerTerm.expandIn program layer)).toOption.isNone
#guard (Checker.checkLayer (source.signature.withParams [slot]) layerPath
  (LayerTerm.expandIn program layer)).toOption.isSome

-- The old invariant constrains no declaration at this admitted layer, for any cell or world.
example (w : Effect4.Program.Typed.World) (cell : DeferredKey) : LayerCellTyped source w layerPath cell := by
  intro l lt node checked
  have layerEq : l = layer := by
    change some (Node.layer layer) = some (Node.layer l) at node
    cases node
    rfl
  subst l
  have refused : (Checker.checkLayer source.signature layerPath
      (LayerTerm.expandIn source.program layer)).toOption = none := by decide
  rw [checked] at refused
  cases refused

-- A closed layer does check under the old signature: the invariant is not always vacuous.
#guard (Checker.checkLayer source.signature [] (.effectDiscard unitProgram)).toOption.isSome

end Test.CX1aMemoReview
