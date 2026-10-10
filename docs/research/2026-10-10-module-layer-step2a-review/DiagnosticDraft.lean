import Effect4.Api

/-! A finite diagnostic compatibility control, placed in PLAN.md. -/
namespace DiagnosticDraft
open Effect4 Effect4.Program

def program : NativeEff :=
  .defs [] .nil (.provideLayer (.ref [2,0]) false (.succeed (.lit .unit))) .nil
#guard !program.layerRefsWF
#guard program.firstRefFault == some ([1,0], [2,0], .noLayer)
#guard Api.explain program == some ⟨[1,0], .referenceIllFormed [2,0] .noLayer⟩
#eval program.firstRefFault
end DiagnosticDraft
