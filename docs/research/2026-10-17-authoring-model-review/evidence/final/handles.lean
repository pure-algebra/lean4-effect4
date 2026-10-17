import probes.E

/-!
# Preview replies: allocation requests are not program values

Finite controls compare the unchanged preview with the existing live session.
No new theorem or planned goal is introduced.
-/

set_option autoImplicit false

namespace FinalAuthoringReviewHandles

open Effect4 Effect4.Program Effect4.Machine Effect4.Store

def app : SigApp := { rows := [Row.hole "resource" (.handle "Resource")] }
def program : NativeEff := .perform (.external 0) (.lit .unit)
def allocation : ExitV := .success (.nat 0)

#guard (Api.check program app).toOption.map (·.certificate.ty.answer) = some (.handle "Resource")
#guard (admitProgram program app).toOption.isSome
#guard Run.Tree.outsideAt program = none
#guard Run.Kit.replyFault app 0 allocation |>.isNone
#guard externalValue [] (.handle "Resource") [] (.nat 0) = some (["Resource"], Value.external 0)
#guard ProofScout.E.checkedTape app 0 .unit [allocation] = some (allocation, [])
#guard match Run.Tree.settle app.rows 10 (ProofScout.E.checkedTape app) [allocation] program with
  | some (_, o) => match o.stop with
    | .finished (.success (.nat 0)) => true
    | _ => false
  | none => false

def live : Option Live := match admitProgram program app with
  | .error _ => none
  | .ok admitted => some ((Live.open ⟨app, program, admitted, []⟩ "handles-review").feed .start).1
def answered : Option Live := live.map fun l =>
  l.feedAll [.receive (.row "resource") (.ofExit allocation), .apply (.row "resource"), .flush]
#guard answered.map (fun l => l.run.inspect.exit) = some (some (.success (Value.external 0)))
#guard Val.memberIn [] (.nat 0) (.handle "Resource") ["Resource"] = false

end FinalAuthoringReviewHandles
