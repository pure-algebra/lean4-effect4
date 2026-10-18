import Effect4.Program.Typing.Suggest
namespace Test.Program.SeamsS3aDifferentEnv
open Effect4 Effect4.Program Program.Check

def source : NativeEff := .succeed (.lit (.nat 0))
def candidate : NativeEff := .succeed (.lit (.nat 1))
def doc : Doc := (Doc.open_ ⟨⟨"candidate",0⟩,{},⟨source,[]⟩⟩).value

#guard match doc.session.focusAt [] with
  | none => false
  | some focus =>
    match (Suggest.suggestOne Oracle.uncached doc focus [] none [.nat] candidate).value with
    | .error _ => false
    | .ok item => item.program == candidate &&
        decide (item.key = .module {} [] candidate) &&
        decide (item.evidence = .differentEnv [.nat] [])
#guard match doc.session.focusAt [] with
  | none => false
  | some focus =>
    (Suggest.suggestOne Oracle.uncached doc focus [] none [.nat] candidate).trace.isEmpty
end Test.Program.SeamsS3aDifferentEnv
