import Effect4.Program.Typing.CheckCache
import Effect4.Program.Typing.FillSet

/-!
# Finite controls for the proposed checking seam

Scope: source focus certification, module layer decomposition, and the five-request trace.
Consumer: the V1 checking seam review at the current source definitions.
Evidence: finite evaluations of existing computations, not proofs of proposed signatures.
No proposed `Check.run`, `combine`, `Memo`, or `Tool.serve` exists in this file.
-/

set_option autoImplicit false

namespace SeamsCheckingControls

open Effect4 Effect4.Program

def nat1 : NativeEff := .succeed (.lit (.nat 1))
def nat2 : NativeEff := .succeed (.lit (.nat 2))
def nat7 : NativeEff := .succeed (.lit (.nat 7))
def natTy : EffTy := .pure .nat

/-! A continuation beside a layer reference has a source focus, but no raw focus. -/

def besideRef : Sketch :=
  { program := .provideLayer (.effectDiscard nat1) false
      (.bind (.provideLayer (.ref [0]) false nat1) (Sketch.hole {} 0))
    holes := [Row.hole "h" .nat] }

#guard besideRef.sourceCheck {} = .ok natTy
#guard (besideRef.focusAt {} [1, 1]).isNone
#guard ((SourceSession.open {} besideRef).focusAt [1, 1]).map (fun f => (f.env, f.ty)) =
  some ([.nat], natTy)
#guard certifiedB besideRef {} [1, 1] (.succeed (.var 0)) = false
#guard (Annotate.check (sketchSigData besideRef {} [1, 1]).signature [.nat] []
  (.succeed (.var 0))).2 = .ok natTy
#guard ((Doc.open {} besideRef).target [1, 1]).map
  (fun t => ((Doc.open {} besideRef).commit t (.fill (.succeed (.var 0)))).toOption.isSome) =
  some true

/-! A reference-bearing filling needs its whole-program expansion context. -/

def refBase : Sketch :=
  { program := .bind (.provideLayer (.effectDiscard nat1) false nat1) nat2 }
def refFilling : NativeEff := .provideLayer (.ref [0, 0]) false nat7

#guard certifiedB refBase {} [1] refFilling = false
#guard ((refBase.fillAt [1] refFilling).map (fun s => s.sourceCheck {})) = some (.ok natTy)
#guard refFilling.expandRefs = refFilling
#guard (Checker.check (({} : SigApp).signature) [.nat] [] refFilling.expandRefs).toOption.isNone

/-! A reference elsewhere invalidates single-site expansion reuse. -/

def referencedBody : Sketch :=
  { program := .provideLayer (.effectDiscard nat1) false
      (.provideLayer (.ref [0]) false nat1) }
def largerBody : NativeEff := .bind nat1 nat7

#guard referencedBody.sourceCheck {} = .ok natTy
#guard certifiedB referencedBody {} [0, 0] largerBody = true
#guard !referencedBody.sites.any (fun site =>
  site = [0, 0] || Path.properPrefix site [0, 0])
#guard ((SourceSession.open {} referencedBody).feed (.fill [0, 0] largerBody)).2 = .rechecked
#guard
  let l := SourceSession.open {} referencedBody
  let direct := (l.expanded.feed (.fill [0, 0] largerBody)).1
  let actual := (l.feed (.fill [0, 0] largerBody)).1
  direct.sketch.program != actual.expanded.sketch.program

/-! The layers wrapper changes addresses and must omit the empty spine. -/

def badLayers : LayerTerms NativeOp :=
  .cons (.effectDiscard (.succeed (.var 0))) .nil

#guard (Checker.refusal (Checker.checkLayers (({} : SigApp).signature) [2] badLayers)).map
  (fun r => r.path) = some [2, 0, 0]
#guard (Checker.refusal (Checker.check (({} : SigApp).signature) [] []
  (Part.layersProgram badLayers))).map (fun r => r.path) = some [0, 0, 0, 0]
#guard (Checker.refusal (Checker.check (({} : SigApp).signature) [] []
  (Part.layersProgram badLayers))).map (fun r => [2] ++ r.path) != some [2, 0, 0]
#guard Checker.checkLayers (({} : SigApp).signature) [2] (.nil : LayerTerms NativeOp) = .ok []
#guard (Checker.check (({} : SigApp).signature) [] []
  (Part.layersProgram (.nil : LayerTerms NativeOp))).toOption.isNone

/-! The reference-free trace uses current commits and the current candidate cache. -/

def trace0 : Doc := Doc.open {}
  { program := .bind nat1 (Sketch.hole {} 0), holes := [Row.hole "h" .nat] }
def trace1 : Option Doc := (trace0.target [1]).bind fun t =>
  (trace0.commit t (.fill (.succeed (.var 0)))).toOption

#guard trace1.map (fun d => d.revision) = some 1
#guard ((trace0.session.feed (.fill [1] (.succeed (.var 0)))).2) = .spliced [[1]]
#guard trace1.bind (fun d => (d.target [0]).map fun t =>
  match d.commit t (.fill (.succeed (.lit (.str "a")))) with
  | .error (.typeChanged _ _) => true
  | _ => false) = some true

def trace2 : Option Doc := trace1.bind fun d => (d.target [0]).bind fun t =>
  (d.commit t (.omitHole "g")).toOption

#guard trace2.map (fun d => (d.revision, d.session.sketch.holes)) =
  some (2, [Row.hole "h" .nat, Row.hole "g" .nat])
#guard trace2.map (fun d => (d.session.feed
  (.fill [0] nat2)).2) = some (.spliced [[0]])

def traceSuggested : Option CheckCache.SuggestResult := trace2.bind fun d =>
  CheckCache.suggest d [] [0] 1 0 [nat2]

#guard traceSuggested.map (fun s => s.suggestions.map (fun x => x.evidence)) =
  some [.exactFit natTy false]
#guard traceSuggested.map (fun s =>
  CheckCache.lookup s.cache ⟨nat2, s.sig, s.env⟩ []) = some (some (.ok natTy))
#guard trace2.bind (fun d => (d.target [0]).bind fun t =>
  (d.commit t (.fill nat2)).toOption.map (fun next => next.revision)) = some 3

end SeamsCheckingControls
