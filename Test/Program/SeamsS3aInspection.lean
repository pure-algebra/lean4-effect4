import Effect4.Tool.Queries
set_option autoImplicit false
namespace Test.Program.SeamsS3aInspection
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

-- A generator's statements are nodes that hold no program. Each such address refuses rather than
-- become a fake program. (`succeed` has no such node: its addresses hold programs only.)
def structured : NativeEff := .gen (.cons (.ret (.lit (.nat 7))) .nil)
def structuredDoc : Doc := (Doc.open_ ⟨⟨"inspect",0⟩,{},⟨structured,[]⟩⟩).value
#guard (Node.addresses (.eff structured)).any fun path =>
  match (Node.eff structured).at_ path with
  | none | some (.eff _) => false
  | some _ => true
#guard (Node.addresses (.eff structured)).all fun path =>
  match (Node.eff structured).at_ path with
  | none | some (.eff _) => true
  | some _ => match Tool.Internal.inspection structuredDoc path with
      | .error (.noProgram refused) => refused == path
      | _ => false
end Test.Program.SeamsS3aInspection
