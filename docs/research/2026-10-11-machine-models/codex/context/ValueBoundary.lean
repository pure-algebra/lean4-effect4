import Effect4.Program.Admission
import Effect4.Program.Compile

/-! Finite controls for the typed-context value boundary.
The executable shape check does not certify service values.
Closed source admission and semantic membership remain separate judgments.
-/
namespace Test.ContextValueBoundary
open Effect4 Effect4.Machine Effect4.Program

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def keys : Effect4.Row ServiceKey := Effect4.Machine.Env.Requirement.single key
def wrong : Ctx := .withServices (Env.Context.empty.addV key (.str "wrong"))

-- Key presence passes even though the declared nat service has a string value.
#guard Val.hasTy (Val.context wrong) (.contextOf keys) []
#guard wrong.services.getV key == some (.str "wrong")
#guard !(Val.hasTy (.str "wrong") .nat [])

-- An open type environment certifies the variable's type, not its runtime value.
#guard (Checker.check (SigApp.signature {}) [.contextOf keys] []
  (.provideContext (.var 0) (.service key))).toOption.isSome

-- Closed source literals and the existing native atom table cannot manufacture this context.
#guard (Checker.check (SigApp.signature {}) [] []
  (.provideContext (.lit (.str "wrong")) (.service key))).toOption.isNone
#guard (Checker.check (SigApp.signature {}) [] []
  (.provideService key (.lit (.str "wrong")) (.service key))).toOption.isNone
#guard nativeAtomTy "const" [] = none
#guard nativeAtomTy "context" [] = none
#guard nativeAtomTy "fiberContext" [.unknown, .nat, .bool] = none

-- Host reply columns cannot introduce the internal context carrier.
def reply : Effect4.Program.Row :=
  { name := "ctxBoundary", spelling := "ctxBoundary", kind := .async,
    request := .unit, answer := .contextOf keys, cite := "finite boundary control",
    registration := .external }
#guard (findInternalHandle [] reply.answer).isSome
#guard (admitSig { rows := [reply] }).toOption.isNone
end Test.ContextValueBoundary
