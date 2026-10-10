import Effect4.Laws.Program.Definitions
import Effect4.Api

/-!
# Definitions whose parameter is a program (decisions row 340): the controls of slices HO-1 and
HO-2

`Program/Checker.lean` types an invocation with programs (`Eff.invoke`) by its definition's row and
each program at its parameter, and `Program/Compile.lean` runs it: the invocation pushes the sites
of its programs on the point's stack, and a parameter's run (`NativeOp.param`) pops back to the
site, at its caller's environment. The checker is sound and complete for the arm
(`check_sound`, `check_complete`, `Laws/Program/Typing/CheckSound.lean`); the compile agrees with
the reference denotation on both hops (`intro_invoke`, `intro_param`,
`Laws/Program/Intro/Sequential.lean`). The example is `twice : number → number`, whose one
parameter `f : number ⇒ number` it runs on its request and then on the answer.

* **Green (tested).** The module is admitted at the declared answer.
* **Red (tested), one per refusal of the arm.** An invocation that passes no program, an
  invocation by `perform` of a definition that takes one, a program above its parameter's
  answer, a parameter's run outside every body, and a body that runs a parameter its definition
  lacks.
* **The run (tested).** Finite runs of the machine at fixed budgets: one invocation; a program
  that a definition passes on, which runs its caller's parameter (the stack's static chain); a
  parameter's run inside a fork that the body forks and joins.
-/

set_option autoImplicit false

namespace Test.Program.InvokeControls

open Effect4 Effect4.Program Effect4.Machine
open Effect4.Machine.Env (Requirement)

/-- A term application by name. -/
def ap (name : String) (args : List Term) : Term :=
  .app name (args.foldr (fun a acc => .cons a acc) .nil)

/-- The checker's signature over the empty application. -/
def sig : Signature NativeOp := ({} : SigApp).signature

/-- The path and the reason's name of a refusal. -/
def refusedAt (r : Except TypeRefusal EffTy) : Option (List Nat × String) :=
  (Checker.refusal r).map fun why => (why.path, why.reason.head)

/-- The value of a successful exit. -/
def successVal : Option ExitV → Option Val
  | some (.success v) => some v
  | _ => none

/-- `f : number ⇒ number`. -/
def fParam : ParamDecl := { name := "f", request := .nat, answer := .nat }

/-- `twice : number → number`, with the parameter `f`. -/
def twiceDecl : DefDecl :=
  { name := "twice", request := .nat, answer := .nat, params := [fParam] }

/-- The body of `twice`: `f` on the request, then on the answer. -/
def twiceBody : NativeEff := .bind (.perform (.param 0) (.var 0)) (.perform (.param 0) (.var 1))

/-- The program `(a) => succeed(succ(a))`, at a caller with no variable. -/
def succArg : Effs NativeOp := .cons (.succeed (ap "succ" [.var 0])) .nil

/-- `twice(5, (a) => succeed(succ(a)))`. -/
def invokeProg : NativeEff := .defs [twiceDecl] (.cons twiceBody .nil) (.invoke 0 (.lit (.nat 5)) succArg)

-- green (tested): the module is admitted at the declared answer
#guard Checker.checkModule sig invokeProg == .ok ⟨.nat, .never, Requirement.empty⟩
#guard Api.typeOf invokeProg == some (EffTy.pure .nat)
-- red (tested): an invocation that passes no program, at the invocation
#guard refusedAt (Checker.checkModule sig
    (.defs [twiceDecl] (.cons twiceBody .nil) (.invoke 0 (.lit (.nat 5)) .nil))) =
  some ([1], "invokeArity")
-- red (tested): `perform` of a definition that takes a program is outside the domain
#guard refusedAt (Checker.checkModule sig
    (.defs [twiceDecl] (.cons twiceBody .nil) (.perform (.call 0) (.lit (.nat 5))))) =
  some ([1], "outsideDomain")
-- red (tested): a program above its parameter's answer, at the program
#guard refusedAt (Checker.checkModule sig
    (.defs [twiceDecl] (.cons twiceBody .nil)
      (.invoke 0 (.lit (.nat 5)) (.cons (.succeed (.lit (.str "a"))) .nil)))) =
  some ([1, 0, 0], "bodyNotDeclared")
-- red (tested): a parameter's run outside every body is outside the domain
#guard refusedAt (Checker.check sig [] [] (.perform (.param 0) (.lit (.nat 5)))) =
  some ([], "outsideDomain")
-- red (tested): a body that runs a parameter its definition lacks, at the run
#guard refusedAt (Checker.checkModule sig
    (.defs [{ twiceDecl with params := [] }] (.cons twiceBody .nil)
      (.perform (.call 0) (.lit (.nat 5))))) =
  some ([0, 0, 0], "outsideDomain")

/-! ## The run -/

/-- `outer : number → number`, with `g : number ⇒ number`: it invokes `twice` with a program that
runs `g`, so `twice`'s parameter runs `outer`'s. -/
def outerDecl : DefDecl :=
  { name := "outer", request := .nat, answer := .nat,
    params := [{ name := "g", request := .nat, answer := .nat }] }

/-- The body of `outer`: `twice(n, (a) => g(a))`. -/
def outerBody : NativeEff := .invoke 0 (.var 0) (.cons (.perform (.param 0) (.var 1)) .nil)

/-- `outer(5, (a) => succeed(succ(a)))`. -/
def forwardProg : NativeEff :=
  .defs [twiceDecl, outerDecl] (.cons twiceBody (.cons outerBody .nil))
    (.invoke 1 (.lit (.nat 5)) succArg)

/-- `forked : number → number`, with `f`: its body forks `f` on its request and joins it. -/
def forkedDecl : DefDecl :=
  { name := "forked", request := .nat, answer := .nat, params := [fParam] }

/-- The body of `forked`. -/
def forkedBody : NativeEff :=
  .bind (.withFiber (.fork (.perform (.param 0) (.var 0)) ⟨true, false, .inherit⟩))
    (.awaitFiber (.var 1) .joinEffect)

/-- `forked(5, (a) => succeed(succ(a)))`. -/
def forkProg : NativeEff :=
  .defs [forkedDecl] (.cons forkedBody .nil) (.invoke 0 (.lit (.nat 5)) succArg)

#guard Api.typeOf forwardProg == some (EffTy.pure .nat)
#guard Api.typeOf forkProg == some (EffTy.pure .nat)
-- tested: one invocation runs its program twice
#guard successVal (Api.run invokeProg 200).exit == some (.nat 7)
-- tested: a program passed on runs its caller's parameter
#guard successVal (Api.run forwardProg 400).exit == some (.nat 7)
-- tested: a parameter's run inside a fork, joined
#guard successVal (Api.run forkProg 400).exit == some (.nat 6)

end Test.Program.InvokeControls
