import Test.Program.InvokeControls
import Effect4.Laws.Program.Author
import Effect4.Library.Ref.Cache

/-!
# Authoring definitions with program parameters, and invocations with programs

Decisions row 340, at the authoring surface (`src/Effect4/Program/Authoring.lean`). A definition
declares its program parameters (`DefSrc.programParams`), its body runs one by its name
(`Param.run`), and a caller invokes it with one program for each (`Def.invokeWith`), which writes
`Eff.invoke k r [p₀, …]`. A program is a Lean function of its parameter's request, read through a
minted name. Each line is a finite evaluation, a control or a reader (decisions row 301).

* **The surface writes the hand trees (tested).** The three programs of the controls of slices
  HO-1 and HO-2 (`Test/Program/InvokeControls.lean`) elaborate to the trees written there, byte
  for byte, and so does the banked Ref cache (`src/Effect4/Library/Ref/Cache.lean`). So the
  checker's arm, the runs and the round trip of the module printer
  (`Test/Codegen/DefinitionsPrint.lean`) that those trees meet are the authored modules' too.
* **Refusals by name (tested).** The scope reader refuses a run of an undeclared parameter, a run
  in a main program, two parameters under one name, and an invocation of an undeclared
  definition, each at its site. The checker refuses an invocation by `Def.invoke` of a definition
  that takes a program, and an invocation with no program.
* **Hygiene (tested).** A program's minted binder leaves a caller's variable reading what it read.
* **Scope (reader).** `authoring_scoped` discharges an authored invocation and a body that passes
  its parameter on, through `Def.invokeWith_scoped` and `Param.run_scoped`
  (`src/Effect4/Laws/Program/Author.lean`).
-/

set_option autoImplicit false

namespace Test.Program.AuthoringInvoke

open Effect4 Effect4.Program Effect4.Program.Authoring
open Test.Program.InvokeControls (fParam twiceDecl twiceBody outerDecl invokeProg forwardProg
  forkProg successVal)

/-- `twice : number → number`, with the parameter `f`: `f` on the request, then on the answer. -/
def twice : DefSrc NativeOp where
  name := "twice"
  params := [("n", .nat)]
  answer := .nat
  programParams := [fParam]
  body
    | [n] => bindWith (Param.run "f" n) fun a => Param.run "f" a
    | _ => succeed unit

/-- `outer : number → number`, with the parameter `g`: `twice` with a program that runs `g`. -/
def outer : DefSrc NativeOp where
  name := "outer"
  params := [("n", .nat)]
  answer := .nat
  programParams := outerDecl.params
  body
    | [n] => Def.invokeWith "twice" [n] [fun a => Param.run "g" a]
    | _ => succeed unit

/-- `forked : number → number`, with `f`: it forks `f` on its request and joins it. -/
def forked : DefSrc NativeOp where
  name := "forked"
  params := [("n", .nat)]
  answer := .nat
  programParams := [fParam]
  body
    | [n] => bindWith (fork (Param.run "f" n)) fun fiber => join fiber
    | _ => succeed unit

/-- The program `(a) => succeed(succ(a))`. -/
def succProgram : ProgramSrc := fun a => succeed (app "succ" [a])

/-- A module of definitions and a main program. -/
def withDefs (defs : List (DefSrc NativeOp)) (main : Src NativeOp) : Module NativeOp :=
  { defs, main }

-- finite evaluation: the surface writes the three trees of the controls, byte for byte
#guard elaborateModule (withDefs [twice] (Def.invokeWith "twice" [nat 5] [succProgram])) =
  .ok invokeProg
#guard elaborateModule (withDefs [twice, outer] (Def.invokeWith "outer" [nat 5] [succProgram])) =
  .ok forwardProg
#guard elaborateModule (withDefs [forked] (Def.invokeWith "forked" [nat 5] [succProgram])) =
  .ok forkProg

/-! ## The banked Ref cache, through the surface -/

/-- The banked cache's three definitions written through the surface: `make` holds `none` at the
cache's type, `get` reads through the cell and runs its loader `load` on a miss, and `invalidate`
empties the cell. -/
def cacheDefs (A E : Ty) : List (DefSrc NativeOp) :=
  [ DefSrc.serviceInit Ref.Cache.serviceName
      { name := "listCacheMake", params := [], answer := Ref.Cache.cellTy A,
        body := fun _ => Ref.make (ascribe (Ref.Cache.cachedTy A) (app "none" [])) },
    DefSrc.serviceMethod Ref.Cache.serviceName "get"
      { name := "listCacheGet", params := [("cell", Ref.Cache.cellTy A)], answer := .list A,
        error := E, programParams := [Ref.Cache.loadParam A E],
        body := fun
          | [cell] => bindWith (Ref.get cell) fun held =>
              selectOptionWith held
                (bindWith (Param.run "load" unit) fun loaded =>
                  andThen (Ref.set cell (app "some" [loaded])) (succeed loaded))
                fun list => succeed list
          | _ => succeed unit },
    DefSrc.serviceMethod Ref.Cache.serviceName "invalidate"
      { name := "listCacheInvalidate", params := [("cell", Ref.Cache.cellTy A)], answer := .unit,
        body := fun
          | [cell] => andThen (Ref.set cell (app "none" [])) (succeed unit)
          | _ => succeed unit } ]

-- finite evaluation: the surface writes the banked block, byte for byte, at two instances
#guard elaborateModule (withDefs (cacheDefs .nat .never) (succeed unit)) =
  .ok (Ref.Cache.block .nat .never)
#guard elaborateModule (withDefs (cacheDefs (.list .string) .string) (succeed unit)) =
  .ok (Ref.Cache.block (.list .string) .string)

/-! ## Refusals by name -/

-- control: a run of a parameter that the definition does not declare, refused at the run
#guard elaborateModule (withDefs
    [{ twice with body := fun | [n] => Param.run "g" n | _ => succeed unit }]
    (Def.invokeWith "twice" [nat 5] [succProgram])) = .error ⟨[0, 0], .unboundParam "g"⟩
-- control: a main program declares no parameter
#guard elaborateModule (withDefs [twice] (Param.run "f" (nat 5))) =
  .error ⟨[1], .unboundParam "f"⟩
-- control: two parameters under one name, refused at the body
#guard elaborateModule (withDefs [{ twice with programParams := [fParam, fParam] }]
    (Def.invokeWith "twice" [nat 5] [succProgram, succProgram])) =
  .error ⟨[0, 0], .duplicateParam "f"⟩
-- control: an invocation of a definition that the module does not declare
#guard elaborateModule (withDefs [twice] (Def.invokeWith "thrice" [nat 5] [succProgram])) =
  .error ⟨[1], .unboundDef "thrice"⟩

/-- The checker's refusal of an authored module: its path and its reason's name. -/
def typingRefusal (m : Module NativeOp) : Option (List Nat × String) :=
  match Api.Author.build m with
  | .error (.typing why) => some (why.path, why.reason.head)
  | _ => none

-- control: `Def.invoke` writes `perform (call k)`, outside the domain of a definition that takes a
-- program
#guard typingRefusal (withDefs [twice] (Def.invoke "twice" [nat 5])) = some ([1], "outsideDomain")
-- control: an invocation with no program
#guard typingRefusal (withDefs [twice] (Def.invokeWith "twice" [nat 5] [])) =
  some ([1], "invokeArity")

/-! ## Hygiene -/

/-- The main program `a = 1; twice(a, (x) => succeed(add(x, a)))`: the program reads its own
request and the caller's `a`. -/
def hygienic : Module NativeOp :=
  withDefs [twice] (bind "a" (succeed (nat 1))
    (Def.invokeWith "twice" [var "a"] [fun x => succeed (app "add" [x, var "a"])]))

-- finite evaluation: the program's minted binder is level 1, and the caller's `a` stays level 0
#guard elaborateModule hygienic =
  .ok (.defs [twiceDecl] (.cons twiceBody .nil)
    (.bind (.succeed (.lit (.nat 1)))
      (.invoke 0 (.var 0) (.cons (.succeed (.app "add" (.cons (.var 1) (.cons (.var 0) .nil)))) .nil)))
    .nil)
-- tested: the module builds and runs `x + 1` twice from 1
#guard ((Api.Author.build hygienic).toOption.map fun b =>
  successVal (Api.run b.program 200).exit) = some (some (.nat 3))

/-! ## Scope -/

-- reader (`Def.invokeWith_scoped`): `authoring_scoped` discharges an authored invocation
example : (Def.invokeWith "twice" [nat 5] [succProgram]).Scoped := by
  unfold succProgram
  authoring_scoped

-- reader (`Param.run_scoped`): and a body that passes its own parameter on
example (n : TermSrc) (hn : n.Scoped) :
    (Def.invokeWith "twice" [n] [fun a => Param.run "g" a]).Scoped := by
  authoring_scoped

end Test.Program.AuthoringInvoke
