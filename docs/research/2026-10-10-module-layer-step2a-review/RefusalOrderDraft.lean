import Effect4.Api

/-! Finite located-refusal controls, placed in PLAN.md. -/
namespace RefusalOrderDraft
open Effect4 Effect4.Program

def unitP : NativeEff := .succeed (.lit .unit)
def leaf : LayerTerm NativeOp := .effectDiscard unitP
def block (layers : LayerTerms NativeOp) : NativeEff := .defs [] .nil unitP layers

def enclosing : NativeEff := block (.cons (.fresh (.fresh (.ref [2,0,0]))) .nil)
def forward : NativeEff := block (.cons (.merge (.ref [2,0,1]) (.fresh leaf)) .nil)
def reference : NativeEff := block (.cons leaf
  (.cons (.merge (.ref [2,0]) (.ref [2,1,0,0])) .nil))
def otherScope : NativeEff := .defs [] .nil
  (.provideLayer (.ref [2,0,0]) false unitP) (.cons (.fresh leaf) .nil)
def mixed : NativeEff := .defs [] .nil
  (.provideLayer (.ref [2,999]) false unitP)
  (.cons (.fresh (.fresh (.ref [2,0,0]))) .nil)

#guard enclosing.firstRefFault == some ([2,0,0,0], [2,0,0], .encloses)
#guard forward.firstRefFault == some ([2,0,0], [2,0,1], .notBefore)
#guard reference.firstRefFault == some ([2,1,0,1], [2,1,0,0], .toReference)
#guard otherScope.firstRefFault == some ([1,0], [2,0,0], .otherScope)
-- First refusal follows source traversal, although the expansion order ranks module paths first.
#guard mixed.firstRefFault == some ([1,0], [2,999], .noLayer)
#guard mixed.refBefore [2,0,0,0] [1,0]
#guard Api.explain mixed == some ⟨[1,0], .referenceIllFormed [2,999] .noLayer⟩
#eval [enclosing.firstRefFault, forward.firstRefFault, reference.firstRefFault,
  otherScope.firstRefFault, mixed.firstRefFault]
end RefusalOrderDraft
