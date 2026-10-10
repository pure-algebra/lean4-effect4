import Effect4.Laws.Program.Typed.Scope
import Test.Program.InvokeControls

/-!
CX1a readers at f00008ee. Concept: residual-program-typing; claim: denote-typed; R4.
Consumers: invocation and parameter arms, and pointTyped_child.
These are concrete readers and finite controls, not a new preservation statement.
The missing outer-domain premise and invalid-address controls delimit the API.
-/
set_option autoImplicit false
namespace Test.CX1aReview
open Effect4 Effect4.Program
open Test.Program.InvokeControls

-- Both definitions and the main program of an admitted forwarding program.
#guard Api.typeOf forwardProg == some (EffTy.pure .nat)
#guard scopeParams forwardProg [] == []
#guard scopeParams forwardProg [0] == []
#guard scopeParams forwardProg [0, 1] == []
#guard scopeParams forwardProg [1] == []
#guard scopeParams forwardProg [0, 0] == twiceDecl.params
#guard scopeParams forwardProg [0, 1, 0] == outerDecl.params
#guard scopeParams forwardProg [0, 1, 0, 0, 0] == outerDecl.params

example : scopeParams forwardProg [0, 1, 0] = outerDecl.params :=
  scopeParams_body (root := forwardProg) (k := 1) rfl rfl

example : scopeParams forwardProg [0, 0, 1] = scopeParams forwardProg [0, 0] :=
  scopeParams_child (root := forwardProg) (path := [0, 0])
    (e := twiceBody) rfl 1

example : scopeParams forwardProg [0, 1, 0, 0, 0] =
    scopeParams forwardProg [0, 1, 0] :=
  scopeParams_below (root := forwardProg) (path := [0, 1, 0]) (e := outerBody)
    rfl (by intro ds bs main h; cases h) [0, 0]

-- A scope lookup is total and does not validate the addressed node.
#guard Node.at_ (.eff forwardProg) [0, 0, 99] == none
#guard scopeParams forwardProg [0, 0, 99] == twiceDecl.params
-- Dropping the non-block premise of scopeParams_below changes the result.
#guard scopeParams forwardProg ([] ++ [0, 0]) != scopeParams forwardProg []

-- Read the repaired parameter-row law at the real module's native signature.
example : ∃ slot, ([fParam] : List ParamDecl)[0]? = some slot ∧
    (sig.withParams [fParam]).rowOf (.param 0) = slot.row.normalizeTypes :=
  Signature.withParams_param sig [fParam] rfl rfl (by decide)

#guard sig.dom (.param 0) == false
#guard (sig.withParams [fParam]).dom (.param 0) == true
#guard (sig.withParams [fParam]).dom (.param 1) == false

-- The corrected premise excludes the old counterexample.
#guard ((sig.withParams [fParam]).withParams []).dom (.param 0) == true
#guard (sig.withParams [fParam]).dom (.param 0) != false
#guard (([] : List ParamDecl)[0]?).isNone

-- Calls retain their declaration rows through a parameter extension.
example :
    ((sig.withDefs [twiceDecl, outerDecl]).withParams outerDecl.params).dom (.call 0) =
      (sig.withDefs [twiceDecl, outerDecl]).dom (.call 0) ∧
    ((sig.withDefs [twiceDecl, outerDecl]).withParams outerDecl.params).rowOf (.call 0) =
      (sig.withDefs [twiceDecl, outerDecl]).rowOf (.call 0) :=
  Signature.withParams_of_none _ _ rfl

example : (sig.withParams [fParam]).serviceTy = sig.serviceTy :=
  Signature.withParams_serviceTy sig [fParam]

example : ((sig.withDefs [twiceDecl]).withParams [fParam]).defOf =
    (sig.withDefs [twiceDecl]).defOf :=
  Signature.withParams_defOf _ [fParam]

end Test.CX1aReview
