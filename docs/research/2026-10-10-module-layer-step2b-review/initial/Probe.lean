import Effect4.Laws.Api.ModuleReadable

/-! Finite controls only. PLAN.md places them against the existing module round trip. -/
namespace ModuleLayerStep2bReview
open Effect4 Effect4.Program

def keyA : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def keyB : ServiceKey := ⟨⟨5⟩, ⟨5⟩⟩
def layerA : LayerTerm NativeOp := .succeed keyA (.nat 7)
def layerB : LayerTerm NativeOp := .merge (.ref [2, 0]) (.succeed keyB (.nat 9))
def layers : LayerTerms NativeOp := .cons layerA (.cons layerB .nil)
def body : NativeEff := .provideLayer (.ref [2, 1, 0]) false (.service keyA)
def block : NativeEff :=
  .defs [{ name := "readModuleKey", request := .unit, answer := .nat }]
    (.cons body .nil)
    (.bind (.perform (.call 0) (.lit .unit)) body) layers

def succeedsWith (p : NativeEff) (n : Nat) : Bool :=
  match (Api.run p 250).exit with
  | some (.success (.nat k)) => k == n
  | _ => false

#guard Api.typeOf block == some (EffTy.pure .nat)
#guard succeedsWith block 7
#guard blockReadable [] (nativeSignature []) block
#guard block.refTargets == []
#guard (Api.printModule "main" block).map (fun m => m.decls.map (·.name)) ==
  some ["readModuleKey", "L_2_0", "L_2_1_0", "main"]
#guard (Api.printModule "main" block).map (fun m =>
  decide (Api.readModule m [] = .ok block)) == some true

-- An ordinary main-program layer still hoists beside module layers.
def mainWithHoist : NativeEff :=
  .bind (.provideLayer (.succeed keyB (.nat 12)) false (.service keyB))
    (.provideLayer (.ref [1, 0, 0]) false body)
def mixed : NativeEff :=
  .defs [{ name := "readModuleKey", request := .unit, answer := .nat }]
    (.cons body .nil) mainWithHoist layers
#guard Api.typeOf mixed == some (EffTy.pure .nat)
#guard succeedsWith mixed 7
#guard mixed.refTargets == [[1, 0, 0]]
#guard blockReadable [] (nativeSignature []) mixed
#guard (Api.printModule "main" mixed).map (fun m => m.decls.map (·.name)) ==
  some ["readModuleKey", "L_2_0", "L_2_1_0", "L_1_0_0", "main"]
#guard (Api.printModule "main" mixed).map (fun m =>
  decide (Api.readModule m [] = .ok mixed)) == some true

-- The reader accepts exactly the contiguous module spine at this split.
#guard moduleLayersOf ([( [2, 0], layerA), ([2, 1, 0], layerB)] ) == some layers
#guard moduleLayersOf ([( [2, 0], layerA), ([1, 0, 0], layerA),
  ([2, 1, 0], layerB)]) == some layers
#guard (moduleLayersOf ([( [2, 1, 0], layerB)])).isNone
#guard (moduleLayersOf ([( [2, 0], layerA), ([2, 0], layerB)])).isNone
#guard (moduleLayersOf ([( [2, 1, 0], layerB), ([2, 0], layerA)])).isNone
#guard (moduleLayersOf ([( [2, 0, 0], layerA)])).isNone

-- A reference to a nested part is refused by admission, even when that part is a layer.
def nestedTarget : NativeEff :=
  .defs [{ name := "identity", request := .unit, answer := .unit }]
    (.cons (.succeed (.var 0)) .nil)
    (.provideLayer (.ref [2, 1, 0, 1]) false (.service keyB)) layers
#guard !Api.wellTyped nestedTarget
#guard (Api.printModule "main" nestedTarget).isNone

-- Per-call body layers remain deferred; this slice admits module references only.
def ownLayer : NativeEff :=
  .defs [{ name := "ownLayer", request := .unit, answer := .nat }]
    (.cons (.provideLayer layerA false (.service keyA)) .nil)
    (.perform (.call 0) (.lit .unit)) .nil
#guard Api.wellTyped ownLayer
#guard (Api.printModule "main" ownLayer).isNone

#eval (block.refTargets, mixed.refTargets, succeedsWith block 7, succeedsWith mixed 7)
end ModuleLayerStep2bReview
