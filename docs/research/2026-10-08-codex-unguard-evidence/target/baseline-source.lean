import Effect4.Api
import Effect4.Codegen.PrintTyped
import TypeScript.Render
import Lean.Data.Json

/-!
# P2b target fixtures at explicit source environments

Each fixture stores a native program and its variable types.
The exporter calls the actual checker and Program.printTyped.
It renders those variable types as TypeScript parameters and leaves the result inferred.
The compiler consumer checks source-derived columns, retaining any mismatches.
These are finite type-only fixtures, not ModuleEmission certificates or host executions.
-/

set_option autoImplicit false

namespace P2bTarget

open Effect4 Effect4.Program Effect4.Codegen TypeScript
open Effect4.Machine.Env (Requirement)
open Lean (toJson)

/-- One finite consumer of the existing program syntax and checker. -/
structure Fixture where
  name : String
  family : String
  env : TyEnv
  program : NativeEff
  expected : EffTy
  companion : String
  joined : Bool

/-- Native atom arguments remain first-order term data. -/
def atom (name : String) (args : List Term) : Term :=
  .app name (args.foldr .cons .nil)

def joined : Ty := .union .nat .string
def fibers : Ty := .union (.fiberOf .nat .never) (.fiberOf .string .bool)
def lists : Ty := .union (.list .nat) (.list .string)
def fiberLists : Ty := .union (.list (.fiberOf .nat .never)) (.list (.fiberOf .string .bool))
def exits : Ty := .union (.exitOf .nat .never) (.exitOf .string .bool)
def causes : Ty := .union (.causeOf .nat) (.exitOf .unit .string)
def records : Ty := .union (.record [("x", false, .nat), ("left", false, .bool)])
  (.record [("x", false, .string), ("right", false, .bool)])
def options : Ty := .union (.option .nat) (.option .string)
def tags : Ty := .union (.prod (.lit "hit") .nat) (.prod (.lit "miss") .string)
-- Hyphenated tags retain the existing structural record target instead of requiring classes.
def recordTags : Ty := .union (.record [("_tag", false, .lit "hit-tag"), ("x", false, .nat)])
  (.record [("_tag", false, .lit "miss-tag"), ("x", false, .string)])

/-- Every joined case has the same-head single-member companion. -/
def twins (name family : String) (unionEnv singleEnv : TyEnv) (p : NativeEff)
    (unionTy singleTy : EffTy) : List Fixture :=
  [ ⟨name ++ "Joined", family, unionEnv, p, unionTy, name ++ "Single", true⟩
  , ⟨name ++ "Single", family, singleEnv, p, singleTy, name ++ "Joined", false⟩ ]

/-- The approved families, including their old single-member target observations. -/
def fixtures : List Fixture :=
  twins "option" "options" [options] [.option .nat]
    (.select (.var 0) .option (.succeed (.lit (.nat 0))) (.succeed (.var 1)))
    (EffTy.pure joined) (EffTy.pure .nat) ++
  twins "foldInferred" "list-fold" [lists, joined] [.list .nat, .nat]
    (.succeed (.fold none (.var 0) (.var 1) (.var 3)))
    (EffTy.pure joined) (EffTy.pure .nat) ++
  [ ⟨"foldStoredJoined", "list-fold", [lists, joined],
      .succeed (.fold (some joined) (.var 0) (.var 1) (.var 3)), EffTy.pure joined,
      "foldStoredSingle", true⟩
  , ⟨"foldStoredSingle", "list-fold", [.list .nat, .nat],
      .succeed (.fold (some .nat) (.var 0) (.var 1) (.var 3)), EffTy.pure .nat,
      "foldStoredJoined", false⟩ ] ++
  twins "fiberJoin" "fibers" [fibers] [.fiberOf .nat .never]
    (.awaitFiber (.var 0) .joinEffect) ⟨joined, .bool, Requirement.empty⟩ (EffTy.pure .nat) ++
  twins "fiberAwait" "fibers" [fibers] [.fiberOf .nat .never]
    (.awaitFiber (.var 0) .awaitValue)
    (EffTy.pure (.exitOf joined .bool)) (EffTy.pure (.exitOf .nat .never)) ++
  twins "fiberInterrupt" "fibers" [fibers] [.fiberOf .nat .never]
    (.withFiber (.interrupt (.var 0))) (EffTy.pure .unit) (EffTy.pure .unit) ++
  twins "fiberRunIn" "fibers" [fibers, Ty.scope] [.fiberOf .nat .never, Ty.scope]
    (.withFiber (.runIn (.var 0) (.var 1))) (EffTy.pure .unit) (EffTy.pure .unit) ++
  twins "fiberInterruptAll" "fibers" [fiberLists] [.list (.fiberOf .nat .never)]
    (.withFiber (.interruptAll (.var 0) none)) (EffTy.pure .unit) (EffTy.pure .unit) ++
  twins "fiberInterruptAllAs" "fibers" [fiberLists] [.list (.fiberOf .nat .never)]
    (.withFiber (.interruptAll (.var 0) (some (.lit (.nat 7)))))
    (EffTy.pure .unit) (EffTy.pure .unit) ++
  twins "fiberAwaitAll" "fibers" [fiberLists] [.list (.fiberOf .nat .never)]
    (.withFiber (.awaitAll (.var 0)))
    (EffTy.pure (.list (.exitOf joined .bool))) (EffTy.pure (.list (.exitOf .nat .never))) ++
  twins "forkChild" "fibers" [joined] [.nat]
    (.withFiber (.fork (.succeed (.var 0)) ⟨true, false, .inherit⟩))
    (EffTy.pure (.fiberOf joined .never)) (EffTy.pure (.fiberOf .nat .never)) ++
  twins "forkDetach" "fibers" [joined] [.nat]
    (.withFiber (.fork (.succeed (.var 0)) ⟨true, true, .inherit⟩))
    (EffTy.pure (.fiberOf joined .never)) (EffTy.pure (.fiberOf .nat .never)) ++
  twins "forkScoped" "fibers" [joined] [.nat]
    (.withFiber (.forkScoped (.succeed (.var 0)) ⟨true, true, .inherit⟩))
    ⟨.fiberOf joined .never, .never, Requirement.single nativeScopeKey⟩
    ⟨.fiberOf .nat .never, .never, Requirement.single nativeScopeKey⟩ ++
  twins "forkIn" "fibers" [joined, Ty.scope] [.nat, Ty.scope]
    (.withFiber (.forkIn (.succeed (.var 0)) ⟨true, true, .inherit⟩ (.var 1)))
    (EffTy.pure (.fiberOf joined .never)) (EffTy.pure (.fiberOf .nat .never)) ++
  twins "scopeClose" "exit-scope" [Ty.scope, exits] [Ty.scope, .exitOf .nat .never]
    (.withFiber (.closeScope (.var 0) (.var 1))) (EffTy.pure .unit) (EffTy.pure .unit) ++
  twins "scoped" "exit-scope" [joined] [.nat]
    (.scoped (.bind (.service nativeScopeKey) (.succeed (.var 0))))
    (EffTy.pure joined) (EffTy.pure .nat) ++
  twins "acquireRelease" "exit-scope" [joined] [.nat]
    (.acquireRelease (.succeed (.var 0)) (.succeed (.lit .unit)))
    ⟨joined, .never, Requirement.single nativeScopeKey⟩
    ⟨.nat, .never, Requirement.single nativeScopeKey⟩ ++
  (["causeIsFail", "causeIsDie", "causeIsInterrupt", "causeError"].flatMap fun name =>
    twins name "cause" [causes] [.causeOf .nat] (.succeed (atom name [.var 0]))
      (EffTy.pure (if name == "causeError" then .option joined else .bool))
      (EffTy.pure (if name == "causeError" then .option .nat else .bool))) ++
  twins "tag" "tag-record" [tags] [.prod (.lit "hit") .nat]
    (.select (.var 0) (.tag "hit") (.succeed (.var 1)) (.succeed (.lit (.str "miss"))))
    (EffTy.pure joined) (EffTy.pure joined) ++
  twins "recordTag" "tag-record" [recordTags] [.record [("_tag", false, .lit "hit-tag"), ("x", false, .nat)]]
    (.select (.var 0) (.recordTag "hit-tag")
      (.succeed (.field .required (.var 1) "x")) (.succeed (.field .required (.var 1) "x")))
    (EffTy.pure joined) (EffTy.pure .nat) ++
  twins "recordRequired" "tag-record" [records] [.record [("x", false, .nat), ("left", false, .bool)]]
    (.succeed (.field .required (.var 0) "x")) (EffTy.pure joined) (EffTy.pure .nat) ++
  twins "recordOptional" "tag-record" [records] [.record [("x", false, .nat), ("left", false, .bool)]]
    (.succeed (.field .optional (.var 0) "x"))
    (EffTy.pure (.union (.option .nat) (.option .string))) (EffTy.pure (.option .nat)) ++
  twins "recordSet" "tag-record" [records] [.record [("x", false, .nat), ("left", false, .bool)]]
    (.succeed (.recordSet (.var 0) "x" (.lit (.bool true))))
    (EffTy.pure (.union (.record [("x", false, .bool), ("left", false, .bool)])
      (.record [("x", false, .bool), ("right", false, .bool)])))
    (EffTy.pure (.record [("x", false, .bool), ("left", false, .bool)]))

/-- Existing target refusals remain located in the template profile. -/
def refusals : List (String × TyEnv × NativeEff × String) :=
  [ ("interruptScoped", [.fiberOf .nat .never], .withFiber (.interruptScoped (.var 0)), "interruptScoped")
  , ("awaitAllFailFast", [.list (.fiberOf .nat .never)], .withFiber (.awaitAllFailFast (.var 0)), "awaitAllFailFast")
  , ("snapshotChildren", [], .withFiber .snapshotChildren, "snapshotChildren")
  , ("awaitNewChildren", [.list (.fiberOf .unknown .unknown)], .withFiber (.awaitNewChildren (.var 0)), "awaitNewChildren")
  , ("forkInChild", [Ty.scope], .withFiber (.forkIn (.succeed (.lit .unit)) ⟨true, false, .inherit⟩ (.var 0)), "forkIn:child")
  , ("forkScopedChild", [], .withFiber (.forkScoped (.succeed (.lit .unit)) ⟨true, false, .inherit⟩), "forkScoped:child") ]

/-- Project the source environment using the production type projection. -/
def parameters (env : TyEnv) : Except String (List Parameter) :=
  env.zipIdx.mapM fun (ty, index) => do
    let some target := Types.ofTy ty | throw ("environment projection refuses " ++ ty.render)
    return { name := Var.name index, type := some target }

/-- Expected types are rendered structural targets, never hand-written TypeScript strings. -/
def columns (ty : EffTy) : Except String Lean.Json := do
  let some answer := Types.ofTy ty.answer | throw "answer projection refuses"
  let some error := Types.ofTy ty.error | throw "error projection refuses"
  return Lean.Json.mkObj [("A", toJson (Render.type house0 answer)),
    ("E", toJson (Render.type house0 error)),
    ("R", toJson (Render.type house0 (requirementType nativeScopeKey ty.requires)))]

/-- Emit one inferred function from the actual typed expression and exact source parameters. -/
def emit (fixture : Fixture) : Except String Lean.Json := do
  let checked ← (Checker.check nativeSignature fixture.env [] fixture.program).mapError
    fun refusal => "checker refuses " ++ fixture.name ++ " at " ++ reprStr refusal.path
  unless checked.answer.normalize = fixture.expected.answer.normalize ∧
      checked.error.normalize = fixture.expected.error.normalize ∧ checked.requires = fixture.expected.requires do
    throw ("unexpected checker columns at " ++ fixture.name)
  let printed ← (Program.printTyped nativeSignature fixture.env fixture.program).mapError reprStr
  let params ← parameters fixture.env
  let initializer : Expr := .lambda params printed
  let decl : ConstDecl := { doc := [], name := fixture.name, value := initializer, exported := true }
  let request : TypeRef := .tuple (← fixture.env.mapM fun ty => do
    let some target := Types.ofTy ty | throw "request projection refuses"
    return target) false
  return Lean.Json.mkObj [("name", toJson fixture.name), ("family", toJson fixture.family),
    ("companion", toJson fixture.companion), ("joined", toJson fixture.joined),
    ("initializer", toJson (Render.expr house0 0 initializer)),
    ("body", toJson (Render.expr house0 0 printed)),
    ("declaration", toJson (Render.constDecl house0 decl)),
    ("columns", ← columns checked), ("request", toJson (Render.type house0 request))]

/-- A retained refusal compares the ordinary and typed printer at the same source. -/
def emitRefusal (fixture : String × TyEnv × NativeEff × String) : Except String Lean.Json := do
  let (name, env, program, reason) := fixture
  let expected : PrintRefusal := .internalAction reason
  let ordinary := print nativeSignature env.length program
  let typed := Program.printTyped nativeSignature env program
  match ordinary, typed with
  | .error ordinaryWhy, .error typedWhy =>
    unless ordinaryWhy = expected ∧ typedWhy = expected do
      throw ("old target refusal changes at " ++ name)
  | _, _ => throw ("old target refusal admits " ++ name)
  return Lean.Json.mkObj [("name", toJson name), ("reason", toJson reason),
    ("checkerAdmits", toJson (Checker.check nativeSignature env [] program).isOk)]

/-- One compact collection, with no execution or raw emission certificate. -/
def manifest : Except String Lean.Json := do
  return Lean.Json.mkObj [("format", toJson "effect4-p2b-target-v1"),
    ("evidence", toJson "finite type-only; actual Program.printTyped; no ModuleEmission certificate"),
    ("fixtures", Lean.Json.arr (← fixtures.mapM emit).toArray),
    ("refusals", Lean.Json.arr (← refusals.mapM emitRefusal).toArray)]

end P2bTarget

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected one output path")
  match P2bTarget.manifest with
  | .error why => throw (IO.userError why)
  | .ok value => IO.FS.writeFile output (value.pretty 100 ++ "\n")
