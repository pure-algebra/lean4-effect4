import Effect4.Api
import Lean

/-! Finite raw-formation controls. PLAN.md places the checked judgment and its limits. -/
set_option autoImplicit false
namespace HO3AnnotationFormation
open Effect4 Effect4.Program

def good : Ty := .record [("item", false, .nat)]
def repeated : Ty := .record [("item", false, .nat), ("item", false, .nat)]
def sample (column : Ty) (callback : Bool) : NativeEff :=
  .defs [{ name := "helper", request := (if callback then .nat else column), answer := .nat, params := (if callback then [{ name := "use", request := column, answer := .nat }] else []) }]
    (.cons (.succeed (.lit (.nat 1))) .nil) (.succeed (.lit (.nat 1))) .nil

def admitted (program : NativeEff) : Bool :=
  match admitProgram program with
  | .ok _ => true
  | .error _ => false

def cases : List (String × NativeEff) :=
  [("callback-good", sample good true), ("callback-repeated", sample repeated true),
   ("ordinary-good", sample good false), ("ordinary-repeated", sample repeated false)]

#guard (Formation.checkInput (sample good true) []).isNone
#guard (Formation.checkInput (sample good false) []).isNone
#guard (Formation.checkInput (sample repeated true) []).isNone
#guard (Formation.checkInput (sample repeated false) []).isSome
#guard Api.wellTyped (sample repeated true)
#guard Api.wellTyped (sample repeated false)
#guard admitted (sample repeated true)
#guard !admitted (sample repeated false)

#eval do
  for (name, program) in cases do
    IO.println <| Lean.Json.compress <| Lean.Json.mkObj
      [("name", Lean.toJson name),
       ("rawFormationAccepted", Lean.toJson (Formation.checkInput program []).isNone),
       ("sourceTypingAccepted", Lean.toJson (Api.wellTyped program)),
       ("programAdmitted", Lean.toJson (admitted program)),
       ("annotationCount", Lean.toJson (Formation.programAnnotations program).length)]
end HO3AnnotationFormation
