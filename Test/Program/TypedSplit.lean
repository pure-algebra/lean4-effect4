import Effect4.Laws.Program.Typed.Assembly

/-!
# M5's reduction and the program as loaded (decisions rows 134, 139, 140 and 153)

The typed corpus's `layer.ref` program (`Test/Program/TypedCorpus.lean`): `Api.typeOf` certifies
the program's expansion (`Program.typeOfProgram`, `Program/Typing.lean`), the checker refuses the
program as written at its reference (`Checker.check`, `Program/Checker.lean`), and `loadR` loads
the program as written, its reference resolved at run time by redirect (`Laws/Program/DenoteR.lean`,
the `.ref` arm). Before decisions row 153 `PointTyped` checked the node as written, so it failed at
this program's root point and `load_typed_of_denotesTyped` carried a reference-free premise. Since
row 153 a node is checked through the expansion's rounds and the reduction has no such premise:
`Test/Program/LayerRefs.lean` (`E4-TYPED-CE-019`). The guards below are unchanged facts about the
program.
-/

namespace Test.Program.TypedSplit
open Effect4 Effect4.Program Effect4.Machine

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

def layerRef : NativeEff :=
  .bind (.provideLayer (.succeed key (.nat 7)) false (.service key))
    (.provideLayer (.ref [0, 0]) false (.service key))

#guard (Api.typeOf layerRef).isSome
#guard (layerRef.refSites []).isEmpty = false
#guard match Checker.check (nativeSignature []) [] [] layerRef with
  | .ok _ => false
  | .error _ => true

end Test.Program.TypedSplit
