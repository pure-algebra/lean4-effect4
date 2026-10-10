import Effect4.Laws.Api.ModuleReadable

/-! Finite controls only. PLAN.md places them against the existing module round trip. -/
namespace ModuleLayerStep2bReview
open Effect4 Effect4.Program

def keyA : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def keyB : ServiceKey := ⟨⟨5⟩, ⟨4⟩⟩
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

def observation (r : Api.Inspection) :=
  (r.outcome, r.exit.isSome, r.exit.bind (fun | .success (.nat n) => some n | _ => none))
#eval (Api.explain block).map (fun r => (r.path, r.reason.head))
#eval observation (Api.run block 250)
#eval observation (Api.run block 2000)
#eval observation (Api.replay block 2000 [Api.evaluate, Api.flush, Api.flush, Api.flush])
#eval (Api.run block 2000).reasons
end ModuleLayerStep2bReview
