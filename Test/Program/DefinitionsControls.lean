import Effect4.Laws.Program.Definitions
import Effect4.Api

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
* **Admission and the run (tested; slice PROC-2).** The program interface admits a block at its
  main program's type, and the frame machine runs it. Finite runs: one invocation, mutual
  recursion through two definitions, recursion without end, which reaches the budget's frontier
  and no failure, and an invocation inside a fork. M5's invocation arm (`call_arm`,
  `Laws/Program/Typed/Denotation.lean`) is the theorem; these are finite evaluations of the
  machine at fixed budgets.
-/

set_option autoImplicit false

namespace Test.Program.DefinitionsControls

open Effect4 Effect4.Program Effect4.Machine
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

/-! ## Admission and the run (slice PROC-2) -/

/-- A term application by name. -/
def ap (name : String) (args : List Term) : Term :=
  .app name (args.foldr (fun a acc => .cons a acc) .nil)

/-- `twice(n) = pair(n, n)`, invoked at 21. -/
def twiceDecl : DefDecl := { name := "twice", request := .nat, answer := .prod .nat .nat }
def twiceProg : NativeEff :=
  .defs [twiceDecl] (.cons (.succeed (ap "pair" [.var 0, .var 0])) .nil)
    (.perform (.call 0) (.lit (.nat 21)))

/-- `isEven` and `isOdd`, each invoking the other on the predecessor, invoked at `k`. -/
def evenOdd (k : Nat) : NativeEff :=
  .defs [{ name := "isEven", request := .nat, answer := .bool },
      { name := "isOdd", request := .nat, answer := .bool }]
    (.cons (.select (ap "isZero" [.var 0]) .bool (.succeed (.lit (.bool true)))
        (.perform (.call 1) (ap "pred" [.var 0])))
      (.cons (.select (ap "isZero" [.var 0]) .bool (.succeed (.lit (.bool false)))
        (.perform (.call 0) (ap "pred" [.var 0]))) .nil))
    (.perform (.call 0) (.lit (.nat k)))

/-- A definition that invokes itself without end. -/
def spinProg : NativeEff :=
  .defs [{ name := "spin", request := .nat, answer := .nat }]
    (.cons (.perform (.call 0) (.var 0)) .nil) (.perform (.call 0) (.lit (.nat 1)))

/-- An invocation inside a fork, joined. -/
def forkProg : NativeEff :=
  .defs [twiceDecl] (.cons (.succeed (ap "pair" [.var 0, .var 0])) .nil)
    (.bind (.withFiber (.fork (.perform (.call 0) (.lit (.nat 4))) ⟨true, false, .inherit⟩))
      (.awaitFiber (.var 0) .joinEffect))

/-- The value of a successful exit. -/
def successVal : Option ExitV → Option Val
  | some (.success v) => some v
  | _ => none

-- tested: the program interface admits each block at its main program's type
#guard Api.typeOf twiceProg == some (EffTy.pure (.prod .nat .nat))
#guard Api.typeOf (evenOdd 7) == some (EffTy.pure .bool)
#guard Api.typeOf spinProg == some (EffTy.pure .nat)
#guard (admitProgram twiceProg).toOption.isSome
-- red (tested): through the interface, one declaration and no body, at the root
#guard (Api.explain (.defs [twiceDecl] .nil (.perform (.call 0) (.lit (.nat 21))))).map
    (fun r => (r.path, r.reason.head)) = some ([], "definitionsMismatch")
-- tested: one invocation answers its body's value
#guard successVal (Api.run twiceProg 200).exit == some (.list [.nat 21, .nat 21])
-- tested: mutual recursion through two definitions
#guard successVal (Api.run (evenOdd 7) 400).exit == some (.bool false)
#guard successVal (Api.run (evenOdd 6) 400).exit == some (.bool true)
-- tested: recursion without end reaches the budget's frontier, with no exit and no failure
#guard (Api.run spinProg 60).outcome == .frontier
#guard (Api.run spinProg 60).exit.isNone
-- tested: an invocation inside a fork, joined
#guard successVal (Api.run forkProg 400).exit == some (.list [.nat 4, .nat 4])

end Test.Program.DefinitionsControls
