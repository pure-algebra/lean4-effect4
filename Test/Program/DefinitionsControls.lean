import Effect4.Laws.Program.Definitions

/-!
# A definition block (decisions row 328): the controls of slice PROC-1

`Program/Definitions.lean` checks a program's definition block at its root, and
`Laws/Program/Definitions.lean` holds its laws: G1 (`defs_conservative`) and G2 (`invoke_hasTy`,
`checkModule_sound`, `checkModule_complete`). The example is one definition, `id : number →
number`, and a main program that invokes it at `5`.

* **Green (tested).** The module is admitted at the declared answer.
* **Red (tested): the main program outside its block.** The checker refuses the invocation as an
  operation outside the domain. So a block is what types an invocation.
* **Red (tested), one per premise of the module judgment.** A body above its declaration, a
  declaration with an open column, a definition the block lacks, a request below the declared
  one, a count of bodies unlike the count of declarations, and a block below the root.
* **G1 at the example (proved).** A main program that invokes nothing is checked the same at the
  block's signature.
-/

set_option autoImplicit false

namespace Test.Program.DefinitionsControls

open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)

/-- `id : number → number`. -/
def idDecl : DefDecl := { name := "id", request := .nat, answer := .nat }

/-- The body of `id`: its request. -/
def idBody : NativeEff := .succeed (.var 0)

/-- The invocation of `id` at `5`. -/
def invokeId : NativeEff := .perform (.call 0) (.lit (.nat 5))

/-- The checker's signature over the empty application. -/
def sig : Signature NativeOp := ({} : SigApp).signature

/-- The path and the reason's name of a refusal. -/
def refusedAt (r : Except TypeRefusal EffTy) : Option (List Nat × String) :=
  (Checker.refusal r).map fun why => (why.path, why.reason.head)

-- green (tested): the module is admitted at the declared answer
#guard Checker.checkModule sig (.defs [idDecl] (.cons idBody .nil) invokeId) ==
  .ok ⟨.nat, .never, Requirement.empty⟩
-- red (tested): the invocation outside its block is outside the domain
#guard refusedAt (Checker.check sig [] [] invokeId) = some ([], "outsideDomain")
-- red (tested): a body whose answer is above its declaration, at the body
#guard refusedAt (Checker.checkModule sig
    (.defs [idDecl] (.cons (.succeed (.lit (.str "a"))) .nil) invokeId)) =
  some ([0, 0], "bodyNotDeclared")
-- red (tested): a declaration with an open column, at the body
#guard refusedAt (Checker.checkModule sig
    (.defs [{ idDecl with answer := .var 0 }] (.cons idBody .nil) invokeId)) =
  some ([0, 0], "definitionColumns")
-- red (tested): an invocation of a definition the block lacks, at the invocation
#guard refusedAt (Checker.checkModule sig
    (.defs [idDecl] (.cons idBody .nil) (.perform (.call 1) (.lit (.nat 5))))) =
  some ([1], "outsideDomain")
-- red (tested): a request that is not below the declared request, at the invocation
#guard refusedAt (Checker.checkModule sig
    (.defs [idDecl] (.cons idBody .nil) (.perform (.call 0) (.lit (.str "x"))))) =
  some ([1], "requestNotSubtype")
-- red (tested): one declaration and no body, at the root
#guard refusedAt (Checker.checkModule sig (.defs [idDecl] .nil invokeId)) =
  some ([], "definitionsMismatch")
-- red (tested): a block below the root, at the block
#guard refusedAt (Checker.checkModule sig
    (.bind (.succeed (.lit (.nat 1))) (.defs [idDecl] (.cons idBody .nil) invokeId))) =
  some ([1], "definitionBlock")

/-- G1 at the example: a main program that invokes nothing is checked the same at the block's
signature. -/
example : Checker.check (sig.withDefs [idDecl]) [] [1] (.succeed (.lit (.nat 1))) =
    Checker.check sig [] [1] (.succeed (.lit (.nat 1))) :=
  defs_conservative sig [idDecl] (e := .succeed (.lit (.nat 1))) trivial [] [1]

end Test.Program.DefinitionsControls
