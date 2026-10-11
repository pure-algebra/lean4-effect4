import Effect4.Api
import Effect4.Codegen.ClassTable

/-! Finite draft-admission controls. PLAN.md places them before investigation. -/
set_option autoImplicit false
namespace HO3PrintReviewNames
open Effect4 Effect4.Program Effect4.Codegen

-- Exact copy of the owner's draft predicate, renamed inside this probe namespace.
def draftParamsNameFault (table : List Row) (name : String) (defs : List DefDecl) :
    List ParamDecl → Option String
  | [] => none
  | q :: qs =>
    if !exportNameSafe q.name || q.name == name || table.any (·.spelling == q.name) ||
        defs.any (·.name == q.name) || qs.any (·.name == q.name) then some q.name
    else draftParamsNameFault table name defs qs


def parameter (name : String) : ParamDecl := { name, request := .nat, answer := .nat }
def qualifiedRow : Row :=
  { name := "widgetRun", spelling := "Widget.run", kind := .program,
    request := .nat, answer := .nat, cite := "probe" }
def trailingRow : Row := { qualifiedRow with spelling := "readWidget", trailing := [.name "Token"] }

#guard draftParamsNameFault [qualifiedRow] "main" [] [parameter "Widget"] == none
#guard draftParamsNameFault [trailingRow] "main" [] [parameter "Token"] == none
#guard draftParamsNameFault [] "main" [] [parameter "Payload"] == none
#guard draftParamsNameFault [qualifiedRow] "main" [] [parameter "use"] == none
#guard draftParamsNameFault [] "main" [] [parameter "a0"] == some "a0"
#guard draftParamsNameFault [] "main" [] [parameter "use", parameter "use"] == some "use"
#guard SourceBindings.qualifiedRoot qualifiedRow.spelling == some "Widget"
#guard RowArg.names trailingRow.trailing == ["Token"]

def payloadFields : List (String × Bool × Ty) := [("_tag", false, .lit "Payload"), ("id", false, .nat)]
def payloadBody : NativeEff := .succeed
  (.record payloadFields ["_tag", "id"]
    (.cons (.lit (.str "Payload")) (.cons (.lit (.nat 7)) .nil)))
def payloadDef : DefDecl :=
  { name := "buildPayload", request := .nat, answer := .record payloadFields,
    params := [parameter "Payload"] }
def payloadBlock : NativeEff :=
  .defs [payloadDef] (.cons payloadBody .nil) (.succeed (.lit .unit)) .nil
#guard Api.wellTyped payloadBlock
#guard (ClassTable.moduleClasses (nativeSignature []) "main" (EffTy.pure .unit) payloadBlock).isOk

-- These service shapes pass the existing hook; HO-3 needs an explicit deferred-profile refusal.
def init : DefDecl :=
  { name := "makeCounter", request := .unit, answer := .nat, role := .serviceInit "Counter" }
def method : DefDecl :=
  { name := "readCounter", request := .nat, answer := .nat,
    role := .serviceMethod "Counter" "read" 0 }
def paramMethod : DefDecl := { method with params := [parameter "use"] }
def paramInit : DefDecl := { init with params := [parameter "use"] }
#guard serviceFault [init, method] == none
#guard serviceFault [init, paramMethod] == none
#guard serviceFault [paramInit, method] == none
#guard match methodClosure init [init, paramMethod] ("read", 1, 0) with
  | .ok (_, .lambda [] (.call (.ident "readCounter") [.ident "a0"]) _) => true
  | _ => false

-- Candidate boundary test only; the owner chooses its located refusal constructor.
def deferredServiceParams (ds : List DefDecl) : Bool := ds.any fun d =>
  match d.role with
  | .plain => false
  | .serviceInit _ | .serviceMethod _ _ _ => !d.params.isEmpty
#guard !deferredServiceParams [init, method]
#guard deferredServiceParams [init, paramMethod]
#guard deferredServiceParams [paramInit, method]
#guard !deferredServiceParams [payloadDef]
#eval (draftParamsNameFault [qualifiedRow] "main" [] [parameter "Widget"],
  serviceFault [init, paramMethod], serviceFault [paramInit, method])
end HO3PrintReviewNames
