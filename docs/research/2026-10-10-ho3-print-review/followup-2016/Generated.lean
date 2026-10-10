import Effect4.Api
import Lean

/-! Finite invocation controls. PLAN.md records the placement and limits. -/
set_option autoImplicit false
namespace HO3InvocationReview
open Effect4 Effect4.Program Effect4.Machine

def q (name : String) : ParamDecl := { name, request := .nat, answer := .nat }
def applyDecl : DefDecl :=
  { name := "applyProgram", request := .nat, answer := .nat, params := [q "use"] }
def applyBody : NativeEff := .perform (.param 0) (.var 0)
def one (p : NativeEff) : Effs NativeOp := .cons p .nil
def moduleOf (main : NativeEff) : NativeEff := .defs [applyDecl] (one applyBody) main .nil

def identity : NativeEff := moduleOf (.invoke 0 (.lit (.nat 5)) (one (.succeed (.var 0))))
def captured (level : Nat) : NativeEff := moduleOf
  (.bind (.succeed (.lit (.nat 11)))
    (.invoke 0 (.lit (.nat 5)) (one (.succeed (.var level)))))
def nested (level : Nat) : NativeEff := moduleOf
  (.bind (.succeed (.lit (.nat 11)))
    (.invoke 0 (.lit (.nat 5))
      (one (.invoke 0 (.lit (.nat 3)) (one (.succeed (.var level)))))))

def relayDecl : DefDecl :=
  { name := "relayProgram", request := .nat, answer := .nat, params := [q "forwarded"] }
def relayBody : NativeEff := .invoke 0 (.var 0) (one (.perform (.param 0) (.var 1)))
def forwarded : NativeEff := .defs [applyDecl, relayDecl]
  (.cons applyBody (.cons relayBody .nil))
  (.bind (.succeed (.lit (.nat 29)))
    (.invoke 1 (.lit (.nat 5)) (one (.succeed (.var 0))))) .nil

def selectedDecl : DefDecl :=
  { name := "selectedProgram", request := .nat, answer := .nat, params := [q "firstTask", q "secondTask"] }
def selected (which : Nat) : NativeEff := .defs [selectedDecl]
  (one (.perform (.param which) (.var 0)))
  (.invoke 0 (.lit (.nat 5))
    (.cons (.succeed (.lit (.nat 11))) (.cons (.succeed (.lit (.nat 17))) .nil))) .nil

def forkedDecl : DefDecl :=
  { name := "forkedProgram", request := .nat, answer := .nat, params := [q "use"] }
def forkedBody : NativeEff :=
  .bind (.withFiber (.fork (.perform (.param 0) (.var 0)) ⟨true, false, .inherit⟩))
    (.awaitFiber (.var 1) .joinEffect)
def forked : NativeEff := .defs [forkedDecl] (one forkedBody)
  (.bind (.succeed (.lit (.nat 37)))
    (.invoke 0 (.lit (.nat 5)) (one (.succeed (.var 0))))) .nil

def cases : List (String × NativeEff × Nat) :=
  [("identity", identity, 5), ("capture-outer", captured 0, 11), ("capture-request", captured 1, 5),
   ("nested-outer", nested 0, 11), ("nested-middle", nested 1, 5), ("nested-inner", nested 2, 3),
   ("forwarded", forwarded, 29), ("select-first", selected 0, 11), ("select-second", selected 1, 17),
   ("forked-capture", forked, 37)]

def result (p : NativeEff) : Option Val := match (Api.run p 600).exit with
  | some (.success value) => some value
  | _ => none

#guard cases.all (fun (_, p, _) => Api.wellTyped p)
#guard cases.all (fun (_, p, expected) => result p == some (.nat expected))
#guard cases.all (fun (_, p, _) => (Api.printModule "main" p).isSome)
#guard cases.all (fun (_, p, _) =>
  ((Api.printModule "main" p).map (fun m => decide (Api.readModule m [] = Except.ok p))) == some true)

-- These are program typing refusals, distinct from raw reconstruction.
#guard !Api.wellTyped (moduleOf (.invoke 0 (.lit (.nat 5)) .nil))
#guard !Api.wellTyped (moduleOf (.invoke 0 (.lit (.nat 5))
  (.cons (.succeed (.lit (.nat 1))) (.cons (.succeed (.lit (.nat 2))) .nil))))
#guard !Api.wellTyped (moduleOf (.invoke 0 (.lit (.nat 5)) (one (.succeed (.lit (.str "bad"))))))
#guard !Api.wellTyped (nested 3)

#eval do
  for (name, p, expected) in cases do
    let some m := Api.printModule "main" p | throw (IO.userError name)
    IO.println <| Lean.Json.compress <| Lean.Json.mkObj
      [("name", Lean.toJson name), ("expected", Lean.toJson expected),
       ("machineBudget", Lean.toJson (600 : Nat)),
       ("machineAgrees", Lean.toJson (result p == some (Val.nat expected))),
       ("readsBack", Lean.toJson (decide (Api.readModule m [] = Except.ok p))),
       ("source", Lean.toJson (TypeScript.Render.module TypeScript.house0 m))]
end HO3InvocationReview
