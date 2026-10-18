import Effect4.Tool.Queries
set_option autoImplicit false
namespace Test.SeamsInspection
open Effect4 Effect4.Program Program.Check Tool

def program : NativeEff := .succeed (.lit (.nat 7))
def doc : Doc := (Doc.open_ ⟨⟨"inspect",0⟩,{},⟨program,[]⟩⟩).value

-- The comparison retains every field read by the frozen S1 inspect branch.
#guard match Tool.Internal.inspection doc [] with
  | .error _ => false
  | .ok found =>
    let entry := doc.session.table.find? fun e => decide (e.path = [])
    decide (found.path = [] ∧ found.expected = program ∧
      found.context = sketchSigData doc.session.sketch doc.session.app [] ∧
      found.focus = doc.session.focusAt [] ∧ found.entry = entry ∧
      found.refusal = entry.bind (fun e => e.result.bind Checker.refusal))

#guard match Tool.Internal.inspection doc [99] with
  | .error (.noProgram [99]) => true
  | _ => false

-- Find a real nonprogram node; its address must refuse rather than become a fake program.
#guard (Node.addresses (.eff program)).any fun path =>
  match (Node.eff program).at_ path with
  | none | some (.eff _) => false
  | some _ => match Tool.Internal.inspection doc path with
      | .error (.noProgram refused) => refused == path
      | _ => false
end Test.SeamsInspection
