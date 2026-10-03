import Effect4.Laws.Program.Typed.Assembly

/-!
# The split `J`/`I` as landed (decisions rows 134, 139, 140)

`#print` shows `J` (`MachineTyped`: `TypedState`, `LiveCode`, `MachineLive`) and `I`
(`ConfigTyped`: `J`, `ReadCode`, `QueueOk`) as the elaborator holds them, with the production
bundle `preds` and the generated scope-state clause the un-refused row now states. `#print axioms`
lists every theorem in `Laws/Program/Typed/Assembly.lean` and `Laws/Program/Typed/Scheduler.lean`
and the ledger's checked theorems; the trust ceiling is `[propext, Quot.sound]`. Reading aid and
axiom list; no claim is made here.
-/

open Effect4.Program.Typed

#print MachineTyped
#print TypedState
#print LiveCode
#print MachineLive
#print ConfigTyped
#print ReadCode
#print ReadsCode
#print QueueOk
#print StepPreserves
#print preds
#print ScopeStateOk
#print SnapshotTyped
#print DecisionEdits
#print DenotesTyped
#print TermFits
#print Reestablishes

/-! ## M5's reduction and the program as loaded

The typed corpus's `layer.ref` program (`Test/Program/TypedCorpus.lean:76`): `Api.typeOf`
certifies the program's expansion (`Program/Typing.lean:61-64`), the checker refuses the program
as written at its reference (`Program/Checker.lean:259`), and `loadR` loads the program as
written, its reference resolved at run time by redirect (`Laws/Program/DenoteR.lean`, the `.ref`
arm). Before decisions row 153 `PointTyped` checked the node as written, so it failed at this
program's root point and `load_typed_of_denotesTyped` carried a reference-free premise. Since row
153 a node is checked through the expansion's rounds and the reduction has no such premise:
`Test/Program/LayerRefs.lean` (`E4-TYPED-CE-019`). The guards below are unchanged facts about the
program. -/

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
