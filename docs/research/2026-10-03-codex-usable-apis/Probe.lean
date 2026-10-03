import Effect4.Api

/-! Finite discriminators for the combined API plan at 6366de3b.
No new production theorem, program representation, or semantic ruling.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace CombinedApiProbe
open Effect4 Effect4.Machine Effect4.Program

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def leaf : LayerTerm NativeOp := .succeed key (.nat 7)
def original : NativeEff :=
  .bind (.provideLayer (.merge leaf leaf) false (.service key))
    (.provideLayer (.ref [0, 0, 0]) false (.service key))
def edited : NativeEff :=
  .bind (.provideLayer leaf false (.service key))
    (.provideLayer (.ref [0, 0, 0]) false (.service key))

-- Equal local layer types; a structural edit still invalidates a remote reference.
#guard layerTy nativeSignature (.merge leaf leaf) = layerTy nativeSignature leaf
#guard (layerTy nativeSignature leaf).isSome
#guard original.layerRefsWF
#guard (typeOfProgram nativeSignature original).isSome
#guard (Node.eff original).replaceLayerAt [0, 0] leaf = some (.eff edited)
#guard !edited.layerRefsWF
#guard (typeOfProgram nativeSignature edited).isNone

-- A read has no writes but observes the other operation's write.
def readThenWrite : Option (Val × RefHeap) := do
  let (answer, heap) ← refStep (.refGet ⟨0⟩) [.nat 0]
  let (_, heap') ← refStep (.refSet ⟨0⟩ (.nat 1)) heap
  pure (answer, heap')
def writeThenRead : Option (Val × RefHeap) := do
  let (_, heap) ← refStep (.refSet ⟨0⟩ (.nat 1)) [.nat 0]
  let (answer, heap') ← refStep (.refGet ⟨0⟩) heap
  pure (answer, heap')
#guard readThenWrite = some (.nat 0, [.nat 1])
#guard writeThenRead = some (.nat 1, [.nat 1])
#guard readThenWrite.map Prod.snd = writeThenRead.map Prod.snd
#guard readThenWrite.map Prod.fst != writeThenRead.map Prod.fst

end CombinedApiProbe
