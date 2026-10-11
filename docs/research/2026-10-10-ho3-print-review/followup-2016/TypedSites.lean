import Effect4.Program.Native
import Effect4.Codegen.PrintTyped
import Lean

/-! Finite typed-site and raw-binder controls; placement is in PLAN.md. -/
set_option autoImplicit false
namespace HO3InvocationTypedReview
open Effect4 Effect4.Program Effect4.Codegen
open TypeScript.Render (expr)
open TypeScript (house0)

def u : Ty := .union .nat .string
def product : Term := .app "tuple" (.cons (.var 0) (.cons (.var 1) .nil))
def d : DefDecl :=
  { name := "useProduct", request := .prod u u, answer := .unit,
    params := [{ name := "use", request := .unit, answer := .unit }] }
def s : Signature NativeOp := nativeSignature.withDefs [d]
def spell : String → List RowArg → Option NativeOp := defsSpell NativeOp.call [d] (nativeSpell [])
def requestSite : NativeEff := .invoke 0 product (.cons (.succeed (.lit .unit)) .nil)
def ordinarySite : NativeEff := .succeed product

def callbackDecl : DefDecl :=
  { name := "useCallback", request := .unit, answer := .prod u u,
    params := [{ name := "use", request := .unit, answer := .prod u u }] }
def callbackSig : Signature NativeOp := nativeSignature.withDefs [callbackDecl]
def callbackSpell : String → List RowArg → Option NativeOp :=
  defsSpell NativeOp.call [callbackDecl] (nativeSpell [])
def callbackSite : NativeEff := .invoke 0 (.lit .unit) (.cons (.succeed product) .nil)

-- Source typing succeeds in both joined contexts.
#guard (Checker.check s [u,u] [] requestSite).isOk
#guard (Checker.check callbackSig [u,u] [] callbackSite).isOk
#guard PrintEliminators.needsSites s [u,u] requestSite
#guard PrintEliminators.needsSites callbackSig [u,u] callbackSite

def missingContext (r : Except PrintRefusal TypeScript.Expr) : Bool := match r with
  | .error (.internalAction name) => name == "typed:missing context"
  | _ => false

-- HO3b-SPINE-01: the typed path requires a context for the empty callback spine.
#guard missingContext (Program.printTyped s [u,u] requestSite)
#guard missingContext (Program.printTyped callbackSig [u,u] callbackSite)
#guard ((PrintEliminators.contextAtTable (annotate s [u,u] requestSite) requestSite) [0,1]).isNone
#guard ((PrintEliminators.contextAtTable (annotate s [u,u] requestSite) requestSite) [0,0]).isSome

-- Positive twins: raw printing succeeds, and a non-joined context uses the raw route.
#guard (print s 2 requestSite).isOk
#guard (print callbackSig 2 callbackSite).isOk
#guard (Checker.check s [.nat,.nat] [] requestSite).isOk
#guard !PrintEliminators.needsSites s [.nat,.nat] requestSite
#guard (Program.printTyped s [.nat,.nat] requestSite).isOk
#guard (Program.printTyped s [u,u] ordinarySite).map (expr house0 0) =
  .ok "Effect.succeed(tuple<number | string, number | string>(a0, a1))"

-- A probe-only algebra override tests the minimal shared repair.
-- It adds no stored syntax and does not change any checked context.
def withEmptySpine (sig : Signature NativeOp) (env : TyEnv) (p : NativeEff) :
    Except PrintRefusal TypeScript.Expr :=
  let entries := annotate sig env p
  let alg := Templates.typedSitesAlg sig (typeArgsAt sig env p)
    (PrintEliminators.contextAtTable entries p)
  cata_eff { alg with effs_nil := fun _ _ => .ok [] } p [] env.length

#guard (withEmptySpine s [u,u] requestSite).isOk
#guard (withEmptySpine callbackSig [u,u] callbackSite).isOk

-- HO3b-TERM-01: after the spine repair, only the invocation request misses site types.
#guard (withEmptySpine s [u,u] requestSite).map (expr house0 0) =
  .ok "useProduct(tuple(a0, a1), (a2) => Effect.succeed(undefined))"
#guard (PrintEliminators.term s [u,u] false product).map (expr house0 0) =
  .ok "tuple<number | string, number | string>(a0, a1)"
#guard (withEmptySpine callbackSig [u,u] callbackSite).map (expr house0 0) =
  .ok "useCallback(undefined, (a2) => Effect.succeed(tuple<number | string, number | string>(a0, a1)))"

def repairedRoundTrip (sig : Signature NativeOp) (sp : String → List RowArg → Option NativeOp)
    (env : TyEnv) (p : NativeEff) : Bool :=
  match withEmptySpine sig env p, print sig env.length p with
  | .ok typed, .ok raw =>
    raw == eraseJoinArgs [] sig sp env.length typed &&
      decide (readTyped [] sig sp env.length typed = .ok p)
  | _, _ => false
#guard repairedRoundTrip s spell [u,u] requestSite
#guard repairedRoundTrip callbackSig callbackSpell [u,u] callbackSite

-- Unrelated joins also select the typed route for the containing program.
def plainRequest : Term := .app "tuple" (.cons (.lit (.nat 1)) (.cons (.lit (.nat 2)) .nil))
def plainInvocation : NativeEff := .invoke 0 plainRequest (.cons (.succeed (.lit .unit)) .nil)
def enclosing : NativeEff := .bind ordinarySite plainInvocation
#guard !PrintEliminators.needsSites s [u,u,.prod u u] plainInvocation
#guard (Program.printTyped s [u,u,.prod u u] plainInvocation).isOk
#guard (Checker.check s [u,u] [] enclosing).isOk
#guard missingContext (Program.printTyped s [u,u] enclosing)
#guard repairedRoundTrip s spell [u,u] enclosing


-- A closed callback alone can trigger the same failure.
def closedDecl : DefDecl :=
  { name := "closedCallback", request := .unit, answer := .prod u u,
    params := [{ name := "use", request := u, answer := .prod u u }] }
def closedSig : Signature NativeOp := nativeSignature.withDefs [closedDecl]
def closedSpell : String → List RowArg → Option NativeOp :=
  defsSpell NativeOp.call [closedDecl] (nativeSpell [])
def closedSite : NativeEff := .invoke 0 (.lit .unit)
  (.cons (.succeed (.app "tuple" (.cons (.var 0) (.cons (.var 0) .nil)))) .nil)
#guard (Checker.check closedSig [] [] closedSite).isOk
#guard PrintEliminators.needsSites closedSig [] closedSite
#guard missingContext (Program.printTyped closedSig [] closedSite)
#guard repairedRoundTrip closedSig closedSpell [] closedSite

-- The source-depth metadata needs an explicit invocation case in its proof consumers.
#guard ((Node.eff requestSite).childEnv s (.env [u,u]) 0).map (fun c => c.tyEnv.length) == some 3

-- Raw callback syntax requires its canonical binder. Typing separately checks arity.
def callbackBody : TypeScript.Expr := .call (.ident "Effect.succeed") [.ident "a0"]
def wrongBinder : TypeScript.Expr := .call (.ident "useProduct")
  [.call (.ident "tuple") [.ident "a0", .ident "a1"], Binders.write 1 [0] callbackBody]
def correctBinder : TypeScript.Expr := .call (.ident "useProduct")
  [.call (.ident "tuple") [.ident "a0", .ident "a1"], Binders.write 2 [0] callbackBody]
#guard !(readEff [] s spell 2 wrongBinder).isOk
#guard (readEff [] s spell 2 correctBinder).isOk
#guard eraseJoinArgs [] s spell 2 wrongBinder == wrongBinder

#eval do
  for (name, sig, env, p) in
      [("invoke-request", s, [u,u], requestSite),
       ("ordinary-term", s, [u,u], ordinarySite),
       ("invoke-callback", callbackSig, [u,u], callbackSite),
       ("enclosing-join", s, [u,u], enclosing),
       ("closed-callback", closedSig, [], closedSite)] do
    let observation := (Program.printTyped sig env p).map (expr house0 0)
    let .ok patched := withEmptySpine sig env p | throw (IO.userError name)
    IO.println <| Lean.Json.compress <| Lean.Json.mkObj
      [("name", Lean.toJson name),
       ("production", Lean.toJson (reprStr observation)),
       ("emptySpineProbe", Lean.toJson (expr house0 0 patched))]
end HO3InvocationTypedReview
