import Effect4.Program.Typing

/-! Small application calls used by the compiler checkpoint. They exercise the production
canonical constructor and all three columns of generator merging, including nonempty rows. -/
namespace Conform.Effect4.NormalizationInputs
open _root_.Effect4 _root_.Effect4.Program _root_.Effect4.Machine.Env

def canonicalRaw (t : Ty) : Ty := (CTy.ofRaw t).toRaw

def mergeColumns (a b : Ty) : Option (Option Ty × Ty × List (Nat × Nat)) := do
  let left : GenTy := ⟨some a, a, Requirement.ofList [⟨⟨2⟩, ⟨7⟩⟩, ⟨⟨1⟩, ⟨3⟩⟩]⟩
  let right : GenTy := ⟨some b, b, Requirement.ofList [⟨⟨1⟩, ⟨3⟩⟩, ⟨⟨4⟩, ⟨9⟩⟩]⟩
  let result ← GenTy.merge left right
  return (result.answer, result.error, result.requires.elems.map fun key => (key.name.value, key.service.value))
end Conform.Effect4.NormalizationInputs
